using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Diagnostics;
using System.Drawing;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows.Forms;

namespace NTRUEncrypt
{

    public partial class Form1 : Form
    {
        NTRUEncrypt ntru = new NTRUEncrypt();

        public class Polynom
        {
            public int[] coef;
            private int n;

            public Polynom(int[] a_i, int count)
            {
                if (a_i.Length < count)
                    throw new ArgumentException("Invalid length of coefficients");

                n = count;
                coef = new int[n];
                Array.Copy(a_i, coef, n);
            }
        }

        public class PolynomMod_q
        {
            public int[] _coef;
            public int _degree;
            public int _q; //mod a

            protected PolynomMod_q() { }

            public PolynomMod_q(int[] a_i, int mod)
            {
                int i = a_i.Length - 1;
                while (a_i[i] % mod == 0 && i > 0)
                    i--;

                _coef = new int[i + 1];
                _degree = i;
                _q = mod;

                for (i = 0; i < _coef.Length; ++i)
                    _coef[i] = (a_i[i] + mod) % mod;
            }

            public Polynom range_coef()
            {
                int[] new_polynom = new int[_coef.Length];

                for (int i = 0; i < new_polynom.Length; i++)
                {
                    if (_coef[i] > _q / 2.0)
                        new_polynom[i] = _coef[i] - _q;
                    else
                        new_polynom[i] = _coef[i];
                }
                return new Polynom(new_polynom, new_polynom.Length);
            }

            public static PolynomMod_q operator +(PolynomMod_q polynom_1, PolynomMod_q polynom_2)
            {
                if (polynom_1._q != polynom_2._q)
                    throw new ArgumentException("Unequal modul polynoms");

                int[] new_polynom = new int[Math.Max(polynom_1._coef.Length, polynom_2._coef.Length)];

                if (polynom_1._degree > polynom_2._degree)
                {
                    Array.Copy(polynom_1._coef, new_polynom, polynom_1._coef.Length);

                    for (int i = 0; i < polynom_2._coef.Length; i++)
                        new_polynom[i] += polynom_2._coef[i];
                }
                else
                {
                    Array.Copy(polynom_2._coef, new_polynom, polynom_2._coef.Length);

                    for (int i = 0; i < polynom_1._coef.Length; i++)
                        new_polynom[i] += polynom_1._coef[i];
                }
                return new PolynomMod_q(new_polynom, polynom_1._q);
            }
            
            public static PolynomMod_q operator -(PolynomMod_q polynom)
            {
                int[] new_polynom = new int[polynom._coef.Length];

                for (int i = 0; i < new_polynom.Length; ++i)
                    new_polynom[i] = -polynom._coef[i];

                return new PolynomMod_q(new_polynom, polynom._q);
            }

            public static PolynomMod_q operator -(PolynomMod_q polynom_1, PolynomMod_q polynom_2)
            {
                return polynom_1 + (-polynom_2);
            }

            public static PolynomMod_q operator *(PolynomMod_q polynom_1, PolynomMod_q polynom_2)
            {
                if (polynom_1._q != polynom_2._q)
                    throw new ArgumentException("Unequal modul polynoms");

                int[] new_polynom = new int[polynom_1._coef.Length + polynom_2._coef.Length];

                for (int i = 0; i < polynom_1._coef.Length; i++)
                    for (int j = 0; j < polynom_2._coef.Length; j++)
                        new_polynom[i + j] += polynom_1._coef[i] * polynom_2._coef[j];

                return new PolynomMod_q(new_polynom, polynom_1._q);
            }

            public static bool operator ==(PolynomMod_q polynom_1, PolynomMod_q polynom_2)
            {
                return polynom_1._coef.SequenceEqual(polynom_2._coef);
            }

            public static bool operator !=(PolynomMod_q polynom_1, PolynomMod_q polynom_2)
            {
                return !(polynom_1 == polynom_2);
            }


        }

        public class PolynomMod_q_n : PolynomMod_q
        {
            private int _n;

            public PolynomMod_q_n(int[] a_i, int mod, int count)
            {
                if (count < a_i.Length)
                    throw new ArgumentException("Invalid degree of coefficients");

                _coef = new int[count];
                _n = count;
                _degree = count - 1;
                _q = mod;

                for (int i = 0; i < a_i.Length; ++i)
                    _coef[i] = (a_i[i] + mod) % mod;

            }

            public static PolynomMod_q_n small_polynom(int count_1, int count_minus_1)
            {
                int[] new_coef = new int[ConstantsNTRU.n];
                Random rand = new Random();

                for (int i = 0; i < ConstantsNTRU.n; i++)
                {
                    if (i < count_1)
                        new_coef[i] = 1;
                    else if (i < count_1 + count_minus_1)
                        new_coef[i] = -1;
                    else new_coef[i] = 0;
                }

                for (int i = ConstantsNTRU.n - 1; i >= 1; i--)
                {
                    int j = rand.Next(i + 1);

                    int tmp = new_coef[j];
                    new_coef[j] = new_coef[i];
                    new_coef[i] = tmp;
                }
                return new PolynomMod_q_n(new_coef, ConstantsNTRU.q, ConstantsNTRU.n);
            }

            public PolynomMod_q_n inverse()
            {
                const int range = 1000;
                int i = 0;
                List<PolynomMod_q> quotients = new List<PolynomMod_q>();

                if (_q == ConstantsNTRU.q)
                    _q = 2;
                int[] x_n_coef = new int[_n + 1];
                x_n_coef[0] = -1;
                x_n_coef[_n] = 1;
                PolynomMod_q x_n = new PolynomMod_q(x_n_coef, _q);
                PolynomMod_q balance = x_n;
                PolynomMod_q f = new PolynomMod_q(_coef, _q);

                int[] f_mod_coef = new int[1];
                PolynomMod_q f_mod = new PolynomMod_q(f_mod_coef, _q);

                int inv_n = inverse_int_mod(f._coef[f._coef.Length - 1]);

                while (balance._degree >= f._degree && i < range)
                {
                    int[] delta_n_coef = new int[balance._degree - f._degree + 1];
                    delta_n_coef[delta_n_coef.Length - 1] = balance._coef[balance._degree] * inv_n;
                    PolynomMod_q delta_n = new PolynomMod_q(delta_n_coef, _q);

                    f_mod = f_mod + delta_n;
                    balance = balance - delta_n * f;
                    i++;
                }
                quotients.Add(f_mod);

                while (balance != new PolynomMod_q(new int[] { 0 }, _q) && i < range)
                {
                    x_n = f;
                    f = balance;
                    f_mod = new PolynomMod_q(new int[_n + 1], _q);
                    balance = x_n;
                    inv_n = inverse_int_mod(f._coef[f._coef.Length - 1]);

                    while (balance._degree >= f._degree && balance != new PolynomMod_q(new int[] { 0 }, _q) && i < range)
                    {
                        int[] delta_n_coef = new int[balance._degree - f._degree + 1];
                        delta_n_coef[delta_n_coef.Length - 1] = balance._coef[balance._degree] * inv_n;
                        PolynomMod_q delta_n = new PolynomMod_q(delta_n_coef, _q);

                        f_mod = f_mod + delta_n;
                        balance = balance - delta_n * f;
                        i++;
                    }
                    quotients.Add(f_mod);
                    i++;
                }
                if (i >= range)
                    throw new Exception("Many iterations");

                List<PolynomMod_q> x = new List<PolynomMod_q>();
                x.Add(new PolynomMod_q(new int[] { 0 }, _q));
                x.Add(new PolynomMod_q(new int[] { 1 }, _q));

                for (int j = 0; j < quotients.Count; j++)
                    x.Add(quotients[j] * x[j + 1] + x[j]);

                if (_q == 2)
                {
                    int n = 2;
                    _q = ConstantsNTRU.q;
                    PolynomMod_q_n f_inverse = new PolynomMod_q_n(x[x.Count - 2]._coef, _q, _n);
                    while (n <= ConstantsNTRU.q)
                    {
                        f_inverse = f_inverse * 2 - this * f_inverse * f_inverse;
                        n *= 2;
                    }
                    return f_inverse;
                }
                PolynomMod_q_n f_inverse2 = new PolynomMod_q_n(x[x.Count - 2]._coef, _q, _n);
                f_inverse2 = f_inverse2 * _q - this * f_inverse2 * f_inverse2;
                return f_inverse2 * 2;
            }

            private int inverse_int_mod(int x)
            {
                for (int i = 1; i < _q; i++)
                    if ((x * i) % _q == 1)
                        return i;

                throw new ArithmeticException("No inverse element");
            }
            
            public static PolynomMod_q_n operator +(PolynomMod_q_n polynom_1, PolynomMod_q_n polynom_2)
            {
                PolynomMod_q res = (polynom_1 as PolynomMod_q) + (polynom_2 as PolynomMod_q);
                return new PolynomMod_q_n(res._coef, polynom_1._q, polynom_1._n);
            }

            public static PolynomMod_q_n operator -(PolynomMod_q_n polynom_1, PolynomMod_q_n polynom_2)
            {
                PolynomMod_q res = (polynom_1 as PolynomMod_q) - (polynom_2 as PolynomMod_q);
                return new PolynomMod_q_n(res._coef, polynom_1._q, polynom_1._n);
            }

            public static PolynomMod_q_n operator *(PolynomMod_q_n polynom_1, PolynomMod_q_n polynom_2)
            {
                if (polynom_1._n != polynom_2._n)
                    throw new ArgumentException("Invalid degree N");

                int[] a_i = new int[polynom_1._n];
                for (int i = 0; i < polynom_1._n; ++i)
                    for (int j = 0; j < polynom_2._n; ++j)
                        a_i[i] += polynom_1._coef[j] * polynom_2._coef[(polynom_1._n + i - j) % polynom_1._n];

                return new PolynomMod_q_n(a_i, polynom_1._q, polynom_1._n);
            }

            public static PolynomMod_q_n operator *(PolynomMod_q_n polynom, int x)
            {
                int[] a_i = new int[polynom._n];
                for (int i = 0; i < polynom._n; ++i)
                    a_i[i] = polynom._coef[i] * x;
                return new PolynomMod_q_n(a_i, polynom._q, polynom._n);
            }

        }

        public class NTRUEncrypt
        {
            private PolynomMod_q_n f, g, h;
            private PolynomMod_q_n f_q, f_p;

            public NTRUEncrypt()
            {
                generate_key();
            }

            public NTRUEncrypt(PolynomMod_q_n[] private_key)
            {
                f = private_key[0];
                f_p = private_key[1];
            }

            public NTRUEncrypt(PolynomMod_q_n public_key)
            {
                h = public_key;
            }

            public int[] byte_to_coef(byte[] array_byte)
            {
                int[] array_int = new int[ConstantsNTRU.n];

                for (int i = 0; i < array_byte.Length * 8; i++)
                    array_int[i] = (array_byte[i / 8] >> (i % 8)) & 1;
                array_int[array_byte.Length * 8] = 1;

                return array_int;
            }

            public byte[] polynom_to_byte(PolynomMod_q_n polynom)
            {
                int count_bit = Convert.ToString(ConstantsNTRU.q - 1, 2).Length;
                byte[] res = new byte[polynom._coef.Length * count_bit / 8 + 1];

                for (int i = 0; i < polynom._coef.Length * count_bit; i++)
                {
                    byte x = (byte)(((polynom._coef[i / count_bit] >> (i % count_bit)) & 1) << (i % 8));
                    res[i / 8] = (byte)(res[i / 8] | x);
                }
                return res;
            }

            public byte[] coef_to_byte(int[] array_int)
            {
                int index = array_int.Length - 1;
                while (array_int[index] != 1)
                    index--;

                if (index % 8 != 0)
                    throw new ArgumentException("Incorrect array");
                byte[] array_byte = new byte[index / 8];

                for (int i = 0; i < index; i++)
                    array_byte[i / 8] = (byte)(array_byte[i / 8] | (array_int[i] << (i % 8)));

                return array_byte;
            }

            public PolynomMod_q_n byte_to_polynom(byte[] array_byte)
            {
                int count_bit = Convert.ToString(ConstantsNTRU.q - 1, 2).Length;
                int[] array_int = new int[array_byte.Length * 8 / count_bit];

                for (int i = 0; i < array_int.Length * count_bit; i++)
                {
                    int x = ((array_byte[i / 8] >> (i % 8)) & 1) << (i % count_bit);
                    array_int[i / count_bit] = array_int[i / count_bit] | x;
                }
                return new PolynomMod_q_n(array_int, ConstantsNTRU.q, ConstantsNTRU.n);
            }
            public byte[] encryption(byte[] array_byte)
            {
                if (h is null)
                    throw new Exception("No encryption key");

                PolynomMod_q_n r = PolynomMod_q_n.small_polynom(ConstantsNTRU.dr, ConstantsNTRU.dr);
                PolynomMod_q_n m = new PolynomMod_q_n(byte_to_coef(array_byte), ConstantsNTRU.q, ConstantsNTRU.n);
                PolynomMod_q_n e = r * h + m;

                return polynom_to_byte(e);
            }

            public byte[] decryption(byte[] array_byte)
            {
                if (f is null || f_p is null)
                    throw new Exception("No decryption key");

                PolynomMod_q_n e = byte_to_polynom(array_byte);
                PolynomMod_q_n a = f * e;
                PolynomMod_q_n new_a = new PolynomMod_q_n(a.range_coef().coef, f_p._q, f_p._degree + 1);
                PolynomMod_q_n m = f_p * new_a;

                return coef_to_byte(m.range_coef().coef);
            }

            public void generate_key()
            {
                while (f_q is null || f_p is null)
                {
                    f = PolynomMod_q_n.small_polynom(ConstantsNTRU.df, ConstantsNTRU.df - 1);
                    g = PolynomMod_q_n.small_polynom(ConstantsNTRU.dg, ConstantsNTRU.dg);
                    PolynomMod_q_n f2 = new PolynomMod_q_n(f.range_coef().coef, ConstantsNTRU.p, ConstantsNTRU.n);

                    f_q = f.inverse();
                    f_p = f2.inverse();
                }
                h = f_q * ConstantsNTRU.p * g;
            }

        }

        public static class ConstantsNTRU
        {
            public static int n = 251;
            public static int p = 3;
            public static int q = 128;

            public static int df = 50;
            public static int dg = 24;
            public static int dr = 16;
        }
        
        public Form1()
        {
            InitializeComponent();
        }

        private void button1_Click(object sender, EventArgs e)
        {
            try
            {
                string s = "";
                StreamReader sr = new StreamReader("in.txt");
                while (!sr.EndOfStream)
                {
                    s += sr.ReadLine() + "\n";
                }
                sr.Close();
                byte[] b = ntru.encryption(Encoding.Default.GetBytes(s));
                var path = "outEncrypt.txt";
                File.WriteAllBytes(path, b);
                MessageBox.Show("Шифрование закончилось!");
                Process.Start("outEncrypt.txt");
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }

        private void button2_Click(object sender, EventArgs e)
        {
            try
            {
                var path = "outEncrypt.txt";
                byte[] data = File.ReadAllBytes(path);
                byte[] b2 = ntru.decryption(data);
                var path2 = "outDecrypt.txt";
                File.WriteAllBytes(path2, b2);
                MessageBox.Show("Расшифрование закончилось!");
                Process.Start("outDecrypt.txt");
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }
    }
}
