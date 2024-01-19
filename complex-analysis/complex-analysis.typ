#import "@local/booxtyp:0.0.2": *

#show: book

#cover(
  [Complex Analysis],
  image("figures/forest.jpg"),
  authors: ("Isaac Fei",),
  bar-color: rgb(67, 118, 108),
)

#outline()

= Complex Numbers

== Algebraic Operations

#definition[
  The set of #index(entry: [complex number])[complex numbers], denoted by $CC$, is
  a field $(RR^2, +, dot)$
  where the addition and multiplication are defined as follows:
  $
    (x_1, y_1) + (x_2, y_2)   &= (x_1 + x_2, y_1 + y_2) \
    (x_1, y_1) dot (x_2, y_2) &= (x_1 x_2 - y_1 y_2, x_1 y_2 + x_2 y_1)
  $<eq:1>
]

Specially, we call $(0, 1) in CC$ the #index[imaginary unit], and denote it by $i$.
Just like representing a vector in $RR^2$ by its components, we can write a
complex number $z$ as
$ z = (x, y) = x (1, 0) + y (0, 1) $
By neglecting the _real unit_ $(1, 0)$ and substitute $i$ for $(0, 1)$, we
obtain the simplified notation
$ z = x + i y $

Moreover, it is evident that
$ i^2 = i dot i &= (0, 1) dot (0, 1) quad & \
              &= (-1, 0)                &"multiplication rule" \
              &= -1 $

Then, with this formula $i^2 = -1$, equations in @eq:1, which are now reduced to
$
  (x_1 + i y_1) + (x_2 + i y_2) &= (x_1 + x_2) + i (y_1 + y_2) \
  (x_1 + i y_1) (x_2 + i y_2)   &= (x_1 x_2 - y_1 y_2) + i (x_1 y_2 + x_2 y_1)
$
can be easily verified by straightforward calculation.

In $RR^2$, the length of a vector $(x, y)$ is defined as $sqrt(x^2 + y^2)$.
Similarly, we define the #index[modulus] or #index[absolute value] of a complex
number $z = x + i y$ as $|z| := sqrt(x^2 + y^2)$, which measure the length or
the magnitude of $z$.

The #index[complex conjugate] of $z = x + i y$ is defined by
$ overline(z) := x - i y $

= Complex Functions

== Limits and Continuity

#lorem(100)

== Holomorphic Functions

#definition[
  Let $f: Omega -> CC$ be a function defined on an open set $Omega subset.eq CC$.
  We say $f$ is #index(entry: [holomorphic functions])[holomorphic] at $z in Omega$ if
  the quotient
  $
    (f(z + h) - f(z)) / h
  $
  converges when $h -> 0$. Its limit is denoted by $f'(z)$ and called the
  derivative of $f$ at $z$. We write
  $
    f'(z) = lim_(h -> 0) (f(z + h) - f(z)) / h
  $
]

#note[
  As we shall see later, if $f$ is holomorphic at $z$, then $f$ must also be
  holomorphic in a neighborhood of $z$.
]

Recall in real analysis, we introduced the concept of infinite derivatives to
handle the problems of vertical tangent lines
@apostolMathematicalAnalysisModern1974.

For example, as illustrated in @fig:2, the function $f(x) = root(3, x), space x in [-1, 1]$ has
a vertical tangent line at $x = 0$. It is by definition not differentiable at $x = 0$.
And hence a lot of theorems do not apply to $f(x) = root(3, x)$ if we assume
functions must be differentiable in some open interval. For instance, we cannot
apply the Mean Value Theorem to $f(x) = root(3, x)$ on $[-1, 1]$ if the
assumption of the theorem requires that $f$ must be differentiable on $(-1, 1)$.
By allowing infinite derivatives, and modifying the assumptions of being
differentiable to the existence of finite or infinite derivatives, we can solve
this problem.

However, in complex analysis usually we shall not consider infinite complex
derivatives.

#figure(image("./figures/cubic-root-function.svg", width: 60%), caption: [
  Cubic root function $f(x) = root(3, x), space x in [-1, 1]$
  and its vertical tangent line at $x=0$.
])<fig:2>

We say $f$ is #index(entry: [holomorphic functions in open sets])[holomorphic in]
an open set $Omega$ if $f$ is holomorphic at every point of $Omega$. Let $E$ be
a closed subset of $CC$. We say $f$ is #index(entry: [holomorphic functions on closed sets])[holomorphic on] $E$ if $f$ is
holomorphic in an open set containing $E$. Finally, if $f$ is holomorphic on $CC$,
we say $f$ is #index(entry: [entire functions])[entire].

#example[
  The simplest example of a holomorphic function is the constant function $f(z) = c$.
  Its derivative is $f'(z) = 0$.
]

#example[
  The function $f(z) = z$ is entire. Its derivative is $f'(z) = 1$.
]

#example[
  The real and image parts of a complex function $f(z) = z$:
  + $Re(z)$
  + $Im(z)$
  are not holomorphic at any point.

  To see $Re(z)$ is not holomorphic, we approach to $z = x + i y, space x, y in RR$ from
  the real and imaginary axes, respectively. Approaching from the real axis, we
  have
  $
    lim_(u -> 0) (Re(z + u) - Re(z)) / u
    = lim_(u -> 0) (Re(x + i y + u) - Re(x + i y)) / u
    = lim_(u -> 0) (x + u - x) / u = 1
  $
  and from the imaginary axis, we have
  $
    lim_(v -> 0) (Re(z + i v) - Re(z)) / (i v)
    = lim_(v -> 0) (Re(x + i y + i v) - Re(x + i y)) / (i v)
    = lim_(v -> 0) (x - x) / (i v) = 0
  $<eq:5>
  where $u, v in RR$. Since the two limits are different, $Re(z)$ is not
  holomorphic at $z$.

  #note[
    In @eq:5, referring to the definition, we really should let $i v -> 0$. But in
    this case, $i v -> 0$ is equivalent to $v -> 0$.
  ]

  A similar argument shows that $Im(z)$ is not holomorphic either.
]

#example[
  The complex conjugate function $f(z) = overline(z)$ is not holomorphic at any
  point. This is because we can write the real and imaginary parts of $z$ as
  $
    Re(z) = (z + overline(z)) / 2 quad "and" quad Im(z) = (z - overline(z)) / (2 i)
  $
  If the conjugate $f(z) = overline(z)$ were to be holomorphic, then the real and
  imaginary parts would also be holomorphic due to @prop:3. But we have shown in
  the previous example that the real and imaginary parts of $z$ are not
  holomorphic. Therefore, $f(z) = overline(z)$ is not holomorphic.
]

#proposition[
  If $f$ and $g$ are holomorphic in an open set $Omega$, then:
  + $f + g$ is holomorphic in $Omega$ and $(f + g)' = f' + g'$.
  + $f dot g$ is holomorphic in $Omega$ and $(f dot g)' = f' g + f g'$.
  + If $g(z_0) != 0$, then $f/g$ is holomorphic at $z_0$ and
    $
      (f / g)'(z_0) = (f'(z_0) g(z_0) - f(z_0) g'(z_0)) / g(z_0)^2
    $
]<prop:3>

== Smooth Curves

A #index[parameterized curve] is a function
$
  gamma: RR supset.eq [a, b] -> CC
$
When studying complex integration, we are always interested in #index[smooth curves].
A curve $gamma = z(t)$ is said to be smooth if
+ $z'(t)$ exists and is continuous on $[a, b]$,
+ and $z'(t) != 0$ for all $t in (a, b)$.

#exercise[
  Show that
  + the curve $gamma_1(t) = t^3 cos 1/t + i t^3 sin 1/t$ is smooth,
  + but $gamma_2(t) = t^2 cos 1/t + i t^2 sin 1/t$ is not
  where $t in [0, b]$ in both cases.
]

#solution[
  We first show that $gamma_1$ is smooth. It is clear $gamma_1$ is differentiable
  in the open interval $(0, b)$
  with derivative
  $
    gamma'_1 (t) = 3 t^2 cos 1/t + t sin 1/t + i (3 t^2 sin 1/t - t cos 1/t),
    quad t in (0, b)
  $<eq:3>
  And $gamma'_1(t)$ is continuous in $(0, b)$. The problem is whether $gamma'_1(t)$ exists
  at the endpoints $t = 0$ and $t = b$. (Well, we can immediately see that $gamma'_1(b)$ exists
  by considering a slightly larger domain $[0, b + delta]$ for some $delta > 0$.)
  When checking the existence of $gamma'_1(0)$, one may suggest to use the
  definition of derivative, which is absolutely correct. However, if we know the
  limit of $gamma'(t)$ exists at an endpoint, then the (one-sided) derivative must
  also exist there and equal to the limit. See @prop:1 for a proof of this fact.
  From @eq:3, we note that
  $
    lim_(t -> 0) gamma'_1(t) = 0 quad
    "and" quad lim_(t -> b) gamma'_1(t) "also exists"
  $
  Therefore, $gamma'_1(t)$ indeed exists on $[0, b]$ and is continuous, which
  satisfies the first condition of smooth curves.

  We also need to show that $gamma'_1(t) != 0$ for all $t in (0, b)$. The equation $gamma'_1(t) = 0$ yields
  $
    cases(3 t^2 cos 1/t + t sin 1/t = 0, 3 t^2 sin 1/t - t cos 1/t = 0)
  $<eq:4>
  Multiplying the second equation by $3t$, we obtain
  $
    cases(3 t^2 cos 1/t + t sin 1/t = 0, 9 t^3 sin 1/t - 3t^2 cos 1/t = 0)
  $
  Adding these two equations to eliminate $3t^2 cos 1/t$, we get
  $
    t (9t^2 + 1) sin 1/t = 0
  $
  Since $t > 0$, we must have $sin 1/t = 0$. But then by plugging $sin 1/t = 0$ into
  the @eq:4, we have $cos 1/t = 0$, which leads to a contradiction because $sin 1/t$ and $cos 1/t$ cannot
  be zero simultaneously. This shows @eq:4 has no solution, and hence $gamma'_1(t) != 0$ for
  all $t in (0, b)$. In conclusion, $gamma_1$ is smooth.

  Now, we show that $gamma_2$ is not a smooth curve. In the open interval $(0, b)$,
  we have
  $
    gamma'_2(t) = 2t cos 1/t + sin 1/t + i (2t sin 1/t - cos 1/t)
  $
  Though the derivative of $gamma_2$ exists at $t = 0$ (one can show by definition
  that $gamma'_2(0) = 0$), it is not continuous there.
]

@fig:1 depicts the two curves $gamma_1$ and $gamma_2$. They look similar to each
other and are smooth in most part. The only problematic point is $t = 0$ for $gamma_2$.

#figure(
  image("figures/two-spirals.svg", width: 60%),
  caption: [
    Left: $gamma_1(t) = t^3 cos 1/t + i t^3 sin 1/t$ is smooth. Right: $gamma_2(t) = t^2 cos 1/t + i t^2 sin 1/t$ is
    not.
  ],
)<fig:1>

#proposition[
  Let $f: [a, b] -> RR$ be a continuous function whose derivative $f'$ exists in $(a, b)$.
  If the limit of $f'$ exists at $a$, then $f'$ also exists at $a$ and
  $ f'_+(a) = lim_(x -> a^+) f'(x) $
  An analogous statement holds for the left-hand derivative at $b$.
]<prop:1>

#proof[
  Suppose $lim_(x -> a^+) f'(x) = L$. Let $epsilon > 0$ be an arbitrary positive
  number. Then there exists $delta > 0$ such that
  $ 0 < x - a < delta ==> |f'(x) - L| < epsilon $<eq:2>
  Let a number $h$ be such that $0 < h < delta$. By the Mean Value Theorem, we
  have
  $
    (f(a + h) - f(a) ) / h = f'(xi)
    quad "for some" xi in (a, a + h)
  $
  It then follows that
  $
    abs((f(a + h) - f(a) ) / h - L) = abs(f'(xi) - L) < epsilon
  $
  where the last inequality is due to @eq:2 since $0 < xi - a < h < delta$. This
  proves that $f$ is differentiable at $a$ and $f'_+(a) = L$.
]

A curve may have multiple parameterizations. For example, $gamma(t) = t + i t, t in [0, 1]$
and $alpha(s) = 1/2 s+ i 1/2 s, s in [0, 2]$ both trace out the same straight
line. But they vary in speed. How can we define the equivalence of two
parameterized curves?

Imagine two particles $P$ and $Q$ are traveling along curves $gamma(t), t in [a, b]$ and $alpha(s), s in [c, d]$,
respectively. suppose $P$ spent time $t$ and arrived at $z = gamma(t)$ (for the $n$-th
time). Then for $Q$ to arrive at the same point $z = alpha(s)$ (for the $n$-th
time), the time it will take, $s$, is certain and hence uniquely determined by $t$.
This gives rise to a function $s = g(t)$.

Moreover, if we think of the previous process in the opposite way, that is,
determined how much time $P$ will take to arrive at $Q$'s position, then we find
that $g$ must be a bijection.

And as particle $P$ spends more time traveling, the spent time of $Q$ must also
increase, which means $g$ is a increasing function.

#definition[
  Let $gamma: [a, b] -> CC$ and $alpha: [c, d] -> CC$ be two parameterized curves.
  We say $gamma$ and $alpha$ are #index(entry: [equivalent parameterizations])[equivalent] via $g$ if
  there exists a bijection $g: [a, b] <-> [c, d]$ such that
  + $g$ is increasing,
  + and $gamma(t) = alpha(g(t))$ for all $t in [a, b]$.
  We also say that $gamma$ and $alpha$ are two #index[reparametrization] of each
  other.
]

A simple observation is that such function $g$ is continuous. See @prop:2.

#proposition[
  If $f: [a, b] -> [c, d]$ is a monotonic surjective function, then $f$ is
  continuous.
]<prop:2>

#proof[
  Without loss of generality, we assume $f$ is increasing. Choose a point $x_0 in [a, b]$.
  In what follows, we only consider $x_0 in (a, b)$ since the proofs for $x_0 = a$ and $x_0 = b$ are
  similar. Let $epsilon > 0$ be sufficiently small so that $f(x_0) plus.minus epsilon in [c, d]$.
  Since $f$ is surjective, there exist $x_1, x_2 in [a, b]$ such that $f(x_1) = f(x_0) - epsilon$ and $f(x_2) = f(x_0) + epsilon$.
  Note that $x_1 < x_0 < x_2$. Let $delta = min(x_0 - x_1, x_2 - x_0)$. Then for
  any $x in [a, b]$ such that $|x - x_0| < delta$, we have
  $x_1 < x < x_2$. It then follows that
  $
    f(x_0) - epsilon = f(x_1) <= f(x) <= f(x_2) = f(x_0) + epsilon
  $
  since $f$ is increasing. This proves that $f$ is continuous at $x_0$.
]

If $gamma$ and $alpha$ are smooth curves, and they are equivalent via $g$, then
apart from continuity, $g$ must enjoy some other nice properties.

== Complex Integration along Curves

// References
#bibliography("complex-analysis.bib", title: "References")

// Indices
#make-index()