#import "@local/booxtyp:0.0.1": *

#show: book

#cover(
  [Complex Analysis],
  image("figures/forest.jpg"),
  authors: ("Isaac Fei",),
  bar-color: rgb(67, 118, 108),
)

#preface(
  )[
  This is a notebook for self-studying complex analysis. I mainly follow the
  structure of the book _Complex Analysis_ by Stein and Shakarchi
  @steinComplexAnalysis2003.
]

#outline()

= Set Theory

== Preimages

Let $f: X -> Y$ be a function between two sets. The #index[preimage] of a subset $S subset.eq Y$ under $f$,
written $f^(-1)(S)$, is defined by
$
  f^(-1)(S) := {x in X | f(x) in S}
$
In other words,
$
  x in f^(-1)(S) <==> f(x) in S
$

#proposition[
  Let $f: X -> Y$ be a function. We have the following properties:
  + $f^(-1)(emptyset) = emptyset$ and $f^(-1)(Y) = X$.
  + $f^(-1)(sect.big_alpha S_alpha) = sect.big_alpha f^(-1)(S_alpha)$.
  + $f^(-1)(S^complement) = (f^(-1)(S))^complement$.
  + $f^(-1)(S_1 without S_2) = f^(-1)(S_1) without f^(-1)(S_2)$.
  + $f^(-1)(union.big_alpha S_alpha) = union.big_alpha f^(-1)(S_alpha)$.
  + $f^(-1)(union.sq.big_alpha S_alpha) = union.sq.big_alpha f^(-1)(S_alpha)$.
]

#proof[
  We prove each property separately.

  *Proof of 1:* The first property is evident.

  *Proof of 2:* We have
  $
    x in f^(-1)(sect.big_alpha S_alpha) &<==> f(x) in sect.big_alpha S_alpha\
                                        &<==> f(x) in S_alpha, space forall alpha in I \
                                        &<==> x in f^(-1)(S_alpha), space forall alpha in I\
                                        &<==> x in sect.big_alpha f^(-1)(S_alpha)
  $

  *Proof of 3:* We have
  $
    x in f^(-1)(S^complement) &<==> f(x) in S^complement\
                              &<==> f(x) in.not S\
                              &<==> x in.not f^(-1)(S)\
                              &<==> x in (f^(-1)(S))^complement
  $

  *Proof of 4:* By applying the second and third property, we have
  $
    f^(-1)(S_1 without S_2) &= f^(-1)(S_1 sect S_2^complement) \
                            &= f^(-1)(S_1) sect f^(-1)(S_2^complement)
                            &"by the second property" \
                            &= f^(-1)(S_1) sect (f^(-1)(S_2))^complement
                            &"by the third property" \
                            &= f^(-1)(S_1) without f^(-1)(S_2)
  $

  *Proof of 5:* Again, we can prove this by applying the second and third
  property:
  $
    f^(-1)(union.big_alpha S_alpha) &= f^(-1)(sect.big_alpha (S_alpha^complement))^complement\
                                    &= (f^(-1)(sect.big_alpha S_alpha^complement))^complement
                                    &"by the third property"\
                                    &= (sect.big_alpha f^(-1)(S_alpha^complement))^complement
                                    &"by the second property"\
                                    &= union.big_alpha (f^(-1)(S_alpha^complement))^complement \
                                    &= union.big_alpha f^(-1)(S_alpha)
                                    &"by the third property"
  $

  *Proof of 6:* This is proved by the first, second and fifth property.
]

= Point-Set Topology

The knowledge from topology is too important to be neglected. Before we start to
study complex analysis, we shall first introduce some basic concepts in
topology.

== Topology

Topology is the collection of all open subsets in a set.

#definition[
  A #index[topology] on a set $X$ is a collection $cal(T)$ of subsets of $X$ having
  the following properties:
  + $emptyset, X in cal(T)$.
  + $cal(T)$ is closed under arbitrary unions, i.e., $U_alpha in cal(T) space forall alpha in I ==> union.big_(alpha in I) U_alpha in cal(T)$.
  + $cal(T)$ is closed under finite intersections, i.e., $U_1, U_2 in cal(T) ==> U_1 sect U_2 in cal(T)$.
]

A set for which a topology has been specified is called a #index(entry: [topological spaces])[topological space],
and is denoted by $(X, cal(T))$. If the topology is clear from the context, we
simply write $X$ instead of $(X, cal(T))$.

#example[
  The only topology on the empty set $emptyset$ is the singleton $cal(T) = {emptyset}$.
]

#example[
  For a set $X$, the topology containing only $emptyset$ and $X$ is called the #index[trivial topology].
]

#example[
  The power set $cal(P)(X)$ of a set $X$ is a topology on $X$, and is referred to
  as the #index[discrete topology].
]

== Continuous Functions

#definition[
  Let $f: X -> Y$ be a function between two topological spaces. We say $f$ is
  continuous if for any open set $U subset.eq Y$, its preimage $f^(-1)(U)$ is also
  open in $X$.
]

== Compact Spaces

A collection $cal(A) = {A_alpha | alpha in I}$ of subsets in $X$ is said to #index(entry: [covering of a topological space])[cover] $X$,
or to be a #index(entry: [covering of a topological space])[covering] or $X$, if
the union $union.big_(alpha in I) A_alpha$ equals $X$.

And a #index(entry: [subcovering of a topological space])[subcovering] $cal(A)'$ of $cal(A)$ is
a subcollection of $cal(A)$ that also covers $X$.

#definition[
  A topological space $X$ is #index(entry: [compact topological spaces])[compact] if
  every open covering of $X$ has a finite subcovering. Formally, if
  $
    X = union.big_(alpha in I) U_alpha
  $
  where each $U_alpha$ is open in $X$, then there exist $alpha_1, ..., alpha_k in I$ such
  that
  $
    X = union.big_(j=1)^k U_(alpha_j)
  $
]

If $Y$ is a subspace of $X$, to check whether $Y$ is compact, it is usually more
convenient to consider the subsets in $X$ rather than those in $Y$.

A collection $cal(A) = {A_alpha | alpha in I}$ of subsets in $X$ is said to
cover subspace $Y$ if $Y subset.eq union.big_(alpha in I) A_alpha$.

The following proposition states that a subspace $Y$ of $X$ is compact if and
only if any open covering of $Y$ in $X$ has a finite subcovering.

#proposition[
  Let $Y$ be a subspace of $X$. Then $Y$ is compact if and only if every open
  covering of $Y$ in $X$ has a finite subcovering.
]

#proof[
  We prove each direction separately.

  *Proof of $==>$:* Suppose $Y$ is compact. Let ${U_alpha | alpha in I}$ be an
  open covering of $Y$ in $X$. Let $V_alpha = U_alpha sect Y, space alpha in I$.
  Note that $V_alpha$ is open in $Y$. Then, due to the compactness of $Y$, there
  exists a finite subset $J$ of the index set $I$, i.e., $J subset.eq I$ and $abs(J) < oo$,
  such that
  $
    Y = union.big_(alpha in J) V_(alpha) = union.big_(alpha in J) (U_alpha sect Y) subset.eq union.big_(alpha in J) U_alpha
  $
  This shows that ${U_alpha | alpha in J}$ is a finite subcovering of $Y$.

  *Proof of $<==$:* Suppose
  $
    Y = union.big_(alpha in I) V_alpha
  $
  where each $V_alpha$ is open in $Y$. There exists $U_alpha$ open in $X$ such
  that $V_alpha = U_alpha sect Y$. Then, we have
  $
    Y = union.big_(alpha in I) V_alpha = union.big_(alpha in I) (U_alpha sect Y) subset.eq union.big_(alpha in I) U_alpha
  $
  By the given condition, there exists a finite subcovering ${U_alpha | alpha in J}$ of $Y$.
  Consequently, $Y subset.eq union.big_(alpha in J) U_alpha$. It then follows that
  $
    Y = (union.big_(alpha in J) U_(alpha)) sect Y = union.big_(alpha in J) (U_alpha sect Y)
    = union.big_(alpha in J) V_alpha
  $
  This proves that ${V_alpha | alpha in J}$ is a finite subcovering of $Y$, and
  hence $Y$ is compact.
]

#theorem[
  Let $X$ be a compact space. If subset $K subset.eq X$ is closed in $X$, then $K$ is
  also compact.
]<thm:3>

Continuous functions preserve compactness.

#theorem[
  Let $f: X -> Y$ be a continuous function between two topological spaces. If
  $X$ is compact, then $f(X)$ is also compact.
]

#proof[
  Let ${V_alpha | alpha in I}$ be an open covering of $f(X)$ in $Y$. Then, we have $f(X) subset.eq union.big_(alpha in I) V_alpha$.
  It follows that $X subset.eq union.big_(alpha in I) f^(-1)(V_alpha)$. Note that ${f^(-1)(V_alpha) | alpha in I}$ is
  an open covering of $X$. Because $X$ is compact, there exists a finite
  subcovering ${f^(-1)(V_alpha) | alpha in J}$ of $X$. Then, the image $f(X)$ can
  be covered by ${V_alpha | alpha in J}$ of $f(X)$. This proves that $f(X)$ is
  compact.
]

The preimage of a compact set under a continuous function is not necessarily
compact.

#example[
  Consider the identity map $id: (a, b] -> RR$. It is continuous. But the preimage $id^(-1)([a, b]) = (a, b]$ is
  not compact.
]

There is a criterion for a space to be compact formulated in terms of closed
sets instead of open sets.

A collection $cal(C) = {C_alpha | alpha in I}$ of closed subsets in $X$ is said
to have the #index(entry: [finite intersection property])[finite intersection property] if
every finite intersection is nonempty, i.e.,
$
  J subset.eq I "and" abs(J) < oo ==> sect.big_(alpha in J) C_alpha != emptyset
$

#theorem[
  A topological space $X$ is compact if and only if every collection $cal(C) = {C_alpha | alpha in I}$ of
  closed subsets in $X$ that has the finite intersection property also has a
  nonempty intersection, i.e., $sect_(alpha in I) C_alpha != emptyset$.
]<thm:4>

#corollary[
  Let $X$ be a compact Hausdorff metric space. If ${C_n}$ is a sequence of
  nonempty closed subsets such that
  $
    C_1 supset.eq C_2 supset.eq dots.c supset.eq C_n supset.eq ...
  $
  and $lim_(n -> oo) diam(C_n) = 0$, then they intersect at exactly one point:
  $
    sect.big_(n = 1)^oo C_n = {x_0}
  $
]<cor:1>

== Connected Spaces

#definition[
  Let $X$ be a topological space. A #index(entry: [separation of topological spaces])[separation] of $X$ is
  a pair of open subsets $U$ and $V$ such that
  + $U != emptyset$ and $V != emptyset$,
  + $U sect V = emptyset$, and
  + $X = U union V$.

  The last two conditions are equivalent to saying that $X$ is contained in the
  disjoint union of $U$ and $V$, i.e., $X subset.eq U union.sq V$.

  If such a separation exists, we say $X$ is #index(entry: [disconnected topological spaces])[disconnected].
  Otherwise, we say $X$ is #index(entry: [connected topological spaces])[connected].
]

#example[
  The empty set $emptyset$ and the entire space $X$ are connected.
]

The following proposition gives a useful characterization of connectedness of a
topological subspace.

#proposition[
  Let $Y subset.eq X$ be a topological subspace of $X$. Then $Y$ is disconnected
  if and only if there exist two open sets $U, V$ in $X$ such that
  + $U sect Y != emptyset$ and $V sect Y != emptyset$,
  + $U sect V = emptyset$, and
  + $Y subset.eq U union V$.
]

Continuous functions preserve connectedness.

#theorem[
  Let $f: X -> Y$ be a continuous function between two topological spaces. If
  $X$ is connected, then $f(X)$ is also connected.
]

#proof[
  Suppose $f(X) subset.eq V_1 union.sq V_2$ where $V_1$ and $V_2$ are open in $Y$ and $V_1 sect f(X) != emptyset$.
  We want to show that $V_2 sect f(X) = emptyset$. Taking the preimage, we have
  $
    X subset.eq f^(-1)(V_1 union.sq V_2) = f^(-1)(V_1) union.sq f^(-1)(V_2)
  $
  Since $f$ is continuous, $f^(-1)(V_1)$ and $f^(-1)(V_2)$ are open in $X$.
  Moreover, $f^(-1)(V_1) != emptyset$ since $V_1 sect f(X) != emptyset$. Because $X$ is
  connected, we must have $f^(-1)(V_2) = emptyset$. This implies $V_2 sect f(X) = emptyset$ as
  desired.
]

#definition[
  A topological space $X$ is #index(entry: [path-connected topological spaces])[path-connected] if
  for any two points $x, y in X$, there exists a continuous function $p: [0, 1] -> X$ such
  that $p(0) = x$ and $p(1) = y$.
]

#example[
  The famous #index(entry: [topologist's sine curve])[topologist's sine curve] is
  a connected but not path-connected topological space. It is the closure $overline(S)$ of
  the set
  $
    S := { (x, sin 1/x) mid(|) x > 0 }
  $
  One can show that
  $
    overline(S) = { (x, sin 1/x) mid(|) x > 0 } union { (0, y) | y in [-1, 1] }
  $
  Its graph is shown in @fig:4.

  #figure(image("./figures/topologist-sine-curve.svg", width: 60%), caption: [
    The topologist's sine curve.
  ])<fig:4>
]

= Complex Numbers and the Complex Plane

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

== Smooth Curves

Using a set of points of describe a curve may not be sufficient because we also
need the direction of a curve at each point. To solve this problem, we think of
a curve as a trajectory of some particle. The position of this particle at time $t$ is
given by a function $z(t)$.

A #index[parameterized curve] is a function
$
  z: RR supset.eq [a, b] -> CC
$
We say curve $gamma$ is traced out by $z(t)$. It is the set $gamma = z([a, b])$.

A complex-valued function $f: [a, b] -> CC$ is differentiable at a point $x in (a, b)$ if
both the real and imaginary parts of $f$ are differentiable at $x$, and its
derivative is given by
$
  f'(x) = [Re(f)]'(x) + i [Im(f)]'(x)
$
The one-sided derivatives are defined similarly.

When we are going to study complex integration, we shall always be interested in #index[smooth curves].
A curve $z: [a, b] -> CC$ is said to be smooth if
+ $z'(t)$ exists and is continuous on $[a, b]$, and
+ $z'(t) != 0$ for all $t in [a, b]$, which means it never vanishes.

#note[
  The derivative $z'$ of a smooth curve $z$ is necessarily finite at the two
  endpoints since it is continuous throughout $[a, b]$. We also say $gamma$ is
  continuously differentiable on $[a, b]$.
]

#exercise[
  Show that
  + the curve $z_1(t) = t^3 cos 1/t + i t^3 sin 1/t$ is smooth,
  + but $z_2(t) = t^2 cos 1/t + i t^2 sin 1/t$ is not
  where $t in [0, b]$ in both cases.
]

#solution[
  We first show that $z_1$ is smooth. It is clear $z_1$ is differentiable in the
  open interval $(0, b)$
  with derivative
  $
    z'_1 (t) = 3 t^2 cos 1/t + t sin 1/t + i (3 t^2 sin 1/t - t cos 1/t),
    quad t in (0, b)
  $<eq:3>
  And $z'_1(t)$ is continuous in $(0, b)$. The problem is whether $z'_1(t)$ exists
  at the endpoints $t = 0$ and $t = b$. (Well, we can immediately see that $z'_1(b)$ exists
  by considering a slightly larger domain $[0, b + delta]$ for some $delta > 0$.)
  When checking the existence of $z'_1(0)$, one may suggest to use the definition
  of derivative, which is absolutely correct. However, if we know the limit of $gamma'(t)$ exists
  at an endpoint, then the (one-sided) derivative must also exist there and equal
  to the limit. See @prop:1 for a proof of this fact. From @eq:3, we note that
  $
    lim_(t -> 0) z'_1(t) = 0 quad
    "and" quad lim_(t -> b) z'_1(t) "also exists"
  $
  Therefore, $z'_1(t)$ indeed exists on $[0, b]$ and is continuous, which
  satisfies the first condition of smooth curves.

  We also need to show that $z'_1(t) != 0$ for all $t in (0, b)$. The equation $z'_1(t) = 0$ yields
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
  be zero simultaneously. This shows @eq:4 has no solution, and hence $z'_1(t) != 0$ for
  all $t in (0, b)$. In conclusion, $z_1$ is smooth.

  Now, we show that $z_2$ is not a smooth curve. In the open interval $(0, b)$, we
  have
  $
    z'_2(t) = 2t cos 1/t + sin 1/t + i (2t sin 1/t - cos 1/t)
  $
  Though the derivative of $z_2$ exists at $t = 0$ (one can show by definition
  that $z'_2(0) = 0$), it is not continuous there.
]

@fig:1 depicts the two curves $z_1$ and $z_2$. They look similar to each other
and are smooth in most part. The only problematic point is $t = 0$ for $z_2$.

#figure(
  image("figures/two-spirals.svg", width: 60%),
  caption: [
    Left: $z_1(t) = t^3 cos 1/t + i t^3 sin 1/t$ is smooth. Right: $z_2(t) = t^2 cos 1/t + i t^2 sin 1/t$ is
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

A curve may have multiple parameterizations. For example, $z(t) = t + i t, t in [0, 1]$
and $w(s) = 1/2 s+ i 1/2 s, s in [0, 2]$ both trace out the same straight line.
But they vary in speed. How can we define the equivalence of two parameterized
curves?

Imagine two particles $P$ and $Q$ are traveling along the same curve $gamma$ in
two different ways $z(t), t in [a, b]$ and $w(s), s in [c, d]$, respectively.
suppose $Q$ spent time $s$ and arrived at $z = z(t)$ (for the $n$-th time). Then
for $P$ to arrive at the same point $z = w(s)$ (for the $n$-th time), the time
it will take, $t$, is certain and hence uniquely determined by $s$. This gives
rise to a function $t = g(s)$.

Moreover, if we think of the previous process in the opposite way, that is,
determined how much time $Q$ will take to arrive at $P$'s position, then we find
that $g$ must be a bijection.

And as particle $P$ spends more time traveling, the spent time of $Q$ must also
increase, which means $g$ is a increasing function.

#definition[
  Let $z: [a, b] -> CC$ and $w: [c, d] -> CC$ be two parameterized curves. We say $z(t)$ and $w(s)$ are #index(entry: [equivalent parameterizations])[equivalent] via $g$ if
  there exists a bijection $g: [c, d] <-> [a, b]$ such that
  + $g$ is increasing,
  + and $z((g(s))) = w(s)$ for all $s in [c, d]$.
  We also say that $z(t)$ and $w(s)$ are two #index[reparametrization] of each
  other.
]

A simple observation is that such function $g$ is continuous. See @prop:2.

#proposition[
  If $f: [c, d] -> [a, b]$ is a monotonic surjective function, then $f$ is
  continuous.
]<prop:2>

#proof[
  Without loss of generality, we assume $f$ is increasing. Choose a point $x_0 in [c, d]$.
  In what follows, we only consider $x_0 in (c, d)$ since the proofs for $x_0 = c$ and $x_0 = d$ are
  similar. Let $epsilon > 0$ be sufficiently small so that $f(x_0) plus.minus epsilon in [a, b]$.
  Since $f$ is surjective, there exist $x_1, x_2 in [c, d]$ such that $f(x_1) = f(x_0) - epsilon$ and $f(x_2) = f(x_0) + epsilon$.
  Note that $x_1 < x_0 < x_2$. Let $delta = min(x_0 - x_1, x_2 - x_0)$. Then for
  any $x in [c, d]$ such that $|x - x_0| < delta$, we have
  $x_1 < x < x_2$. It then follows that
  $
    f(x_0) - epsilon = f(x_1) <= f(x) <= f(x_2) = f(x_0) + epsilon
  $
  since $f$ is increasing. This proves that $f$ is continuous at $x_0$.
]

If $z(t)$ and $w(s)$ are smooth curves, and they are equivalent via $g$, then
apart from continuity, $g$ must enjoy some other nice properties.

== Topology on the Complex Plane

The #index[open disk] of radius $r$ centered at $z_0$ is the set
$
  D(z_0, r) := { z in CC | |z - z_0| < r }
$
The #index[closed disk] of radius $r$ centered at $z_0$ is the set
$
  overline(D)(z_0, r) := { z in CC | |z - z_0| <= r }
$

The complex plane $CC$ is endowed with the #index[Euclidean topology]. A subset $Omega$ in $CC$ is
open if and only if for every point $z in Omega$, there exists an open disk $D(z, r) subset.eq Omega$ for
some $r > 0$.

In complex analysis, because we will define the integration of a complex
function along a curve, we are especially interested in the sets in which every
two points can be joined by a curve.

We say a set $S subset.eq CC$ is #index(entry: [curve-connected sets in $CC$])[curve-connected] if
any two points in $S$ can be joined by a piecewise smooth curve in $S$. Note
that this is not a common term. We introduce it to be concise in the following
discussion.

Recall that a curve is a piecewise continuously differentiable function.
Therefore, a path-connected set may not be good enough at a first glance since a
path $p$ is only continuous. However, we shall see in the next theorem that if
an open set $Omega subset.eq CC$ is path-connected, then it is also
curve-connected. And in fact, we only need to assume $Omega$ is connected
because all these three conditions about connectedness are equivalent.

#theorem[
  Let $Omega in CC$ be an open set. Then the following statements are equivalent:
  + $Omega$ is connected.
  + $Omega$ is path-connected.
  + $Omega$ is curve-connected.
]<thm:8>

#proof[
  We prove 1 $==>$ 3 $==>$ 2 $==>$ 1.

  *Proof of 1 $==>$ 3:* Suppose $Omega$ is connected. Fix a point $z_0 in Omega$.
  Let $U$ be the set of all points in $Omega$ that can be joined to $z_0$ by a
  curve, i.e.,
  $
    U = {z in Omega mid(|) "There exits a piecewise smooth" gamma: [a, b] -> Omega "from" z_0 "to" z}
  $
  And let $V = Omega - U$, which means $V$ is the set of all points in $Omega$ that
  cannot be joined to $z_0$ by a curve. Clearly $U$ and $V$ are disjoint. We now
  claim that $U$ and $V$ are open sets.

  To see $U$ is open, let $z in U$. Because $Omega$ is open, there exists an open
  disk $D(z, r) subset.eq Omega$. We want to show it is also contained in $U$,
  i.e., $D(z, r) subset.eq U$. Pick any point $w in D(z, r)$. We need to show $w in U$,
  which means we need to find a curve from $z_0$ to $w$. Since $z in U$, there
  exists a curve $alpha$ from $z_0$ to $z$. Then, we can join $z$ and $w$ by a
  line segment $beta$. After that, we can travel from $z_0$ to $w$ by first
  passing through $alpha$ and then $beta$, which gives us a curve $gamma$ from $z_0$ to $w$.
  See @fig:3 for an illustration.

  #figure(
    image("./figures/piecewise-smooth-curve-from-z0-to-w.svg", width: 60%),
    caption: [
      Construction of a piecewise smooth curve from $z_0$ to $w$.
    ],
  )<fig:3>

  Formally, $beta: [0, 1] -> Omega$ is given by
  $
    beta(t) = (1 - t) z + t w, quad t in [0, 1]
  $
  We claim
  + $beta$ is well-defined, and
  + $beta$ is a smooth curve.

  By the well-definedness, we mean $beta(t)$ is always in $Omega$ for all $t in [0, 1]$.
  To see this, we consider the distance from $beta(t)$ to $z$:
  $
    abs(beta(t) - z) &= abs((1 - t) z + t w - z) quad& \
                     &= abs(t (w - z)) \
                     &= t abs(w - z)                 &"since" t >= 0\
                     &< t r                          & "since" w in D(z, r)\
                     &<= r                           & "since" t <= 1
  $
  Hence, $beta(t) in D(z, r), space forall t in [0, 1]$, which is indeed
  well-defined. Our second claim that $beta$ is smooth is evident since $beta'$ exists,
  and it is continuous and never vanishes.

  Let $gamma = alpha * beta$. Clearly, $gamma$ is a piecewise smooth curve from $z_0$ to $w$ since $alpha$ is
  piecewise smooth and $beta$ is smooth. Therefore, by the definition of $U$, we
  have $w in U$. Because $w in D(z, r)$ is arbitrarily chosen, it follows that $D(z, r) subset.eq U$,
  which further implies that $U$ is open.

  Now, we show that $V$ is also open. Let $z in V$. There exists an open disk $D(z, r) subset.eq Omega$ since $Omega$ is
  open. We want to show $D(z, r) subset.eq V$, that is, to show there is no curve
  from $z_0$ to $w$ for any $w in D(z, r)$. Assume that there exits a piecewise
  smooth curve $gamma$ from $z_0$ to $w$. By applying the same argument as above
  when we proved $U$ is open, we can construct a (smooth) line segment $beta$ from $z$ to $w$.
  Now, let $alpha$ be the curve obtained by joining $gamma$ and $beta^-$, i.e., $alpha = gamma * beta^-$.
  Then, one can show that $alpha$ is a piecewise smooth curve from $z_0$ to $z$ using
  the a similar argument we did before. This leads to a contradiction since there
  cannot be a curve from $z_0$ to $z$ be the definition of $V$. Therefore, our
  assumption that there exists a curve from $z_0$ to $w$ is false, and hence $w in V$,
  which further implies that $D(z, r) subset.eq V$. This proves $V$ is open.

  So far, we have shown that both $U$ and $V$ are open and $Omega = U union.sq V$.
  We also note that $U != emptyset$ since $z_0 in U$. This is because that the
  constant function $gamma: t |-> z_0$ is a smooth curve from $z_0$ to $z_0$. Now,
  because $Omega$ is connected, by definition, we must have $V = emptyset$.
  equivalently, $Omega = U$, which means $Omega$ every point in $Omega$ can be
  joined to $z_0$ by a curve.

  *Proof of 3 $==>$ 2:* The proof of this direction is trivial since loosely
  speaking, every curve is a path. Let $z, w in Omega$. There exists a curve $gamma: [a, b] -> Omega$ from $z$ to $w$.
  Let $p: [0, 1] -> Omega$ be given by
  $
    p(t) = gamma((1-t)a + t b), quad t in [0, 1]
  $
  Note that $p$ is continuous since both $gamma$ and $t |-> (1-t) a + t b$ are
  continuous. Notice also that $t(0) = z$ and $t(1) = w$. Therefore, $p$ is indeed
  a path from $z$ to $w$. Hence, $Omega$ is path-connected.

  *Proof of 2 $==>$ 1:* Finally,we need to show $Omega$ is connected given that it
  is path-connected. We shall prove by contradiction. Assume on the contrary that $Omega$ is
  not connected. Then, there exist two nonempty open sets $U, V subset.eq CC$ such
  that $Omega = U union.sq V$. Suppose $z in U$ and $w in V$. There exists a path $p: [0, 1] -> Omega$ from $z$ to $w$.
  Let
  $
    t^* = sup { t in [0, 1] mid(|) p(s) in U, space forall s in [0, t]}
  $<eq:9>
  Note that $t^*$ exists since $[0, 1]$ is bounded above. Consider the point $p(t^*)$.
  Loosely speaking, $p(t^*)$ is somewhat the point that separates $U$ and $V$. We
  now show $p(t^*)$ cannot be either in $U$ or $V$ to reach a contradiction.

  Suppose first $p(t^*) in U$. Then, there exists an open disk $D(p(t^*), epsilon) subset.eq U$ for
  some $r > 0$ since $U$ is open. Note that the preimage $p^(-1)[D(p(t^*, epsilon))]$ must
  be open in $[0, 1]$ because $p$ is continuous. But
  $
    p^(-1)[D(p(t^*, epsilon))] = [0, t^*]
  $
  due to the definition of $t^*$. This implies that $t^* = 1$. Then, $p(t) in U, space forall t in [0, 1]$,
  which leads to a contradiction since $p(1) = w in V$ and $U sect V = emptyset$.

  We have seen $p(t^*) in.not U $. Then, we must have $p(t^*) in V$. Because $V$ open,
  there exists an open disk $D(p(t^*), epsilon) subset.eq V$. Since $p$ is
  continuous, there exists $delta > 0$ such that
  $
    p(t) in D(p(t^*), epsilon) subset.eq V quad forall t in (t^* - delta, t^* + delta)
  $
  In particular, $p(t^* - delta/2) in V$. This contradicts @eq:9.

  Therefore, $p(t^*) in.not U$ and $p(t^*) in.not V$, which contradicts $Omega = U union.sq V$.
  In conclusion, $Omega$ is connected.
]

= Complex Functions

== Limits and Continuity

If $f$ is a real-valued continuous function defined on a closed interval $[a, b]$,
then we know $f$ attains its maximum and minimum values there. Since we cannot
compare complex numbers, we we cannot define the maximum and minimum values of a
complex functions. But we can instead consider the modulus. Then an analogous
result for complex functions holds, which says the modulus $|f|$ attains its
maximum and minimum values on a compact set $K subset.eq CC$.

In the following, we will prove a slightly more general result.

#theorem[
  Let $K$ be a compact topological space. If $f: K -> RR$ is continuous, then $f$ attains
  its maximum and minimum values on $K$.
]<thm:5>

#proof[
  We will only prove that $f$ attains its maximum value on $K$. The proof for the
  minimum value of $f$ is similar. The general idea is as follows. We will first
  show that $f$ is bounded on $K$, and hence it has a supremum $M$. And then we
  will show that $f$ may take the value $M$.

  *Proof of $f$ Being Bounded:* Consider a collection of open intervals in $RR$:
  $
    V_x = (f(x) - epsilon, f(x) + epsilon), quad x in K
  $
  where $epsilon > 0$ is a fixed positive number. Because $f$ is continuous, the
  preimage $f^(-1)(V_x)$ is open in $K$. And we note that ${f^(-1)(V_x) | x in K}$ forms
  an open cover for $K$. Then because $K$ is compact, there exists a finite
  subcovering, say ${f^(-1)(V_(x_j)) | j=1,...,k}$. We have
  $
          & K subset.eq union.big_(j=1)^k f^(-1)(V_(x_j)) \
    ==> & x in union.big_(j=1)^k f^(-1)(V_(x_j)) quad forall x in K\
    ==> & f(x) in union.big_(j=1)^k V_(x_j) quad forall x in K\
    ==> & min_(1 <= j <= m) f(x_j) - epsilon < f(x) < max_(1 <= j <= m) f(x_j) + epsilon quad forall x in K
  $
  This shows that $f$ is bounded on $K$.

  *Proof of That $f$ May Attain Its Supremum:* Since the range $f(K)$ is bounded
  above, there exists a supremum $M$. We now show that $f(x_0) = M$ for some $x_0 in K$.
  Consider a sequence of closed intervals in $RR$:
  $
    I_n = [M - 1/n, M], quad n in ZZ^+
  $
  The preimage $f^(-1)(I_n)$ is closed in $K$ since $f$ is continuous. Note that
  $
    f^(-1)(I_1) supset.eq f^(-1)(I_2) supset.eq dots.c supset.eq f^(-1)(I_n) supset.eq ...
  $
  And each of them is nonempty since $M$ is the supremum of $f(K)$, which means
  there always exists some $x_n in K$ such that $f(x_n) > M - 1/n$. Therefore, by
  @thm:4, the intersection of all theses closed preimages is nonempty. In other
  words, there exists at least one $x_0 in X$ such that
  $
    x_0 in sect.big_(n=1)^oo f^(-1)(I_n)
  $
  Then, the value $f(x_0)$ satisfies
  $
    M - 1/n <= f(x_0) <= M quad forall n in ZZ^+
  $
  This implies $f(x_0) = M$. Therefore, $M$ is indeed the maximum value of $f$ on $K$.
]

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

#theorem(
  title: [Chain Rule],
)[
  Let $Omega, U subset.eq CC$ be open subsets. If $f: Omega -> U$ and $g: U -> CC$ are
  holomorphic, then the composite function $g compose f$ is also holomorphic in $Omega$ and
  its derivative is given by
  $
    (g compose f)'(z) = g'(f(z)) f'(z), quad z in Omega
  $
]

== Power Series

Recall in real analysis, we defined the number $e$ as
$
  e := sum_(n=0)^oo 1 / n!
$
and the exponential function $exp: RR -> RR$ as the power series
$
  exp(x) := sum_(n=0)^oo x^n / n!, quad x in RR
$<eq:8>
Then, we showed an important property:
$
  exp(x + y) = exp(x) exp(y), space forall x, y in RR
$<eq:6>
By applying @eq:6, it is easy to prove
+ $exp(n) = e^n, space forall n in NN$
+ $exp(1/n) = root(n, e) space forall n in NN$, which is proven by showing $(exp(1/n))^n = e$

It then follows that $exp(x)$ agrees with $e^x$ for every rational number $x in QQ$.
This tells us that we can extend the exponents of $e$ to real numbers:
$
  e^x := exp(x), quad x in RR
$

Now, we can take one step further and extend the exponents of $e$ to complex
numbers. Define
$
  exp(z) := sum_(n=0)^oo z^n / n!, quad z in CC
$<eq:7>
When $z in RR$, @eq:7 reduces to @eq:8.

== Contour Integration

Think about how to integrate a complex-valued function $f$ of a real variable $x$ on
a closed interval $[a, b]$. Naturally, the result should be a complex number
whose real part is the integral of $Re(f)$ and imaginary part is the integral of $Im(f)$.

#definition[
  Let $f: [a, b] -> CC$ be a complex valued function. Suppose that $Re(f)$ and $Im(f)$ are
  both integrable on $[a, b]$. We define the #index[complex integral] of $f$ on $[a, b]$ by
  $
    integral_a^b f(x) dif x := integral_a^b Re[f(x)] dif x + i integral_a^b Im[f(x)] dif x
  $<eq:10>
]<def:1>

#theorem(
  title: [Change of Variables],
)[
  Suppose $g: [c, d] -> RR$ has a continuous derivative $g'$ on $[c, d]$. Let $f$ be
  a real-valued continuous function on $g([c, d])$. Let $F$ be defined by
  $
    F(x) = integral_(g(c))^x f(t) dif t, quad x in g([c, d])
  $
  Then, for each $x in [c, d]$, the integral $integral_c^x f(g(t)) g'(t) dif t$ exists
  and has value $F(g(x))$, i.e.,
  $
    integral_c^x f(g(t)) g'(t) dif t = F(g(x)) quad forall x in [c, d]
  $<eq:12>
  In particular, putting $x = d$ in @eq:12, we obtain the change of variables
  formula:
  $
    integral_(g(c))^g(d) f(x) dif x = integral_c^d f(g(t)) g'(t) dif t
  $
]<thm:1>

#theorem(
  title: [Change of Variables for Complex-Valued Functions],
)[
  Suppose $g: [c, d] -> RR$ has a continuous derivative $g'$ on $[c, d]$. Let $f$ be
  a complex-valued continuous function on $g([c, d])$. Let $F$ be defined by
  $
    F(t) = integral_(g(c))^t f(x) dif x, quad t in g([c, d])
  $
  Then, for each $s in [c, d]$, the integral $integral_c^s f(g(x)) g'(x) dif x$ exists
  and has value $F(g(s))$, i.e.,
  $
    F(g(s)) = integral_c^s f(g(x)) g'(x) dif x quad forall s in [c, d]
  $<eq:13>
  In particular, putting $s = d$ in @eq:13, we obtain the change of variables
  formula:
  $
    integral_(g(c))^g(d) f(t) dif t = integral_c^d f(g(s)) g'(s) dif s
  $
]<thm:2>

#proof[
  By @def:1, we have
  $
    Re[F(t)] = integral_(g(c))^t Re[f(x)] dif x quad "and" quad
    Im[F(t)] = integral_(g(c))^t Im[f(x)] dif x quad forall t in [c, d]
  $
  Apply @thm:1 to both $Re(f)$ and $Im(f)$, we have
  $
    Re[F(g(s))] &= integral_c^s Re[f(g(x))] g'(x) dif x quad forall s in [c, d] \
    Im[F(g(s))] &= integral_c^s Im[f(g(x))] g'(x) dif x quad forall s in [c, d]
  $
  This yields @eq:13. The change of variables formula follows from @eq:13.
]

Thanks to the parameterizations of curves, we can reduce the complex integral of
a general complex function along a curve to the one like @eq:10.

#definition[
  Let $gamma$ be a smooth curve parameterized by $z: [a, b] -> CC$, and $f$ a
  continuous function on $gamma$. Then the #index(
    entry: [complex integral of a function along a curve],
  )[complex integral of $f$ along $gamma$] or the #index[contour integral] is
  defined by
  $
    integral_gamma f(z) dif z := integral_a^b f(z(t)) z'(t) dif t
  $<eq:11>
]

Recall for the same curve $gamma$, there may be multiple different but
equivalent parameterizations. And hence for different parameterizations, we have
different expressions on the right-hand side of @eq:11. However, we shall see
that the complex integral of a function along a curve is independent of the
parameterization, which means the integral is indeed well-defined.

Suppose $z: [a, b] -> CC$ and $w: [c, d] -> CC$ are two parameterizations of the
same curve $gamma$, and they are equivalent via $g: [c, d] -> [a, b]$. We need
to show
$
  integral_a^b f(z(t)) z'(t) dif t = integral_c^d f(w(s)) w'(s) dif s
$
Since $g$ has a continuous derivate on $[c, d]$, we may apply @thm:2. We have
$
  integral_a^b f(z(t)) z'(t) dif t &= integral_g(c)^g(d) f(z(t)) z'(t) dif t \
                                   &= integral_c^d f(z(g(s))) z'(g(s)) g'(s) dif s \
                                   &= integral_c^d f(z(g(s))) dif / (dif s)[z(g(s))] dif s \
                                   &= integral_c^d f(w(s)) dif / (dif s) w(s) dif s \
                                   &= integral_c^d f(w(s)) w'(s) dif s
$
This proves $integral_gamma f(z) dif z$ is independent of parameterizations.

If $gamma$ is a piecewise smooth curve, then the integral of $f$ along $gamma$ is
defined by the sum of the integrals of $f$ along each smooth piece of $gamma$.
Formally, suppose $gamma = gamma_1 * dots.c * gamma_n$ where each $gamma_j$ is
smooth. Then define
$
  integral_gamma f(z) dif z := sum_(j=1)^n integral_(gamma_j) f(z) dif z
$

The length of a smooth curve $gamma = z(t), space t in [a, b]$ is defined by
$
  len(gamma) := integral_a^b abs(z'(t)) dif t
$<eq:14>
#note[
  The integral in @eq:14 exists because $abs(z'(t))$ is continuous on $[a, b]$.
  The definition of length of a curve does not even require the knowledge of
  complex integrals since $abs(z'(t))$ is a real-valued function. And one should
  verify that @eq:14 is also independent of parameterizations.
]
Of course, the length of a piecewise smooth curve is defined by the sum of the
length of each smooth piece.

#proposition[
  Complex integrals of continuous functions along curves satisfy the following
  properties:
  + If $alpha, beta in CC$, then
    $
      integral_gamma (alpha f(z) + beta g(z)) dif z = alpha integral_gamma f(z) dif z + beta integral_gamma g(z) dif z
    $
  + Let $gamma^-$ be the curve of $gamma$ with reverse orientation. Then
    $
      integral_(gamma^-) f(z) dif z = - integral_gamma f(z) dif z
    $
]

#proof[
  We prove each property as follows.

  *Proof of 1:* The first property is proved by applying the linearity of
  integrals of the real and imaginary parts of $f$ on each smooth piece of $gamma$.

  *Proof of 2:* It suffices to prove for the case that $gamma$ is smooth. Let $gamma = z(t), space t in [a, b]$.
  Then $gamma^- = z(b + a - s), space s in [a, b]$. We have
  $
    integral_(gamma^-) f(z) dif z &= integral_a^b f(z(b+a-s)) 1 / (dif s) [z(b+a-s)] dif s \
                                  &= integral_a^b f(z(b+a-s)) (-1) z'(b+a-s) dif s \
                                  &= - integral_a^b f(z(b+a-s)) z'(b+a-s) dif s \
                                  &"Apply change of variables" t = g(s) = b+a-s \
                                  &= - integral_b^a f(z(t)) z'(t) dot (-1) dif t quad "Note" a "and" b "are switched"\
                                  &= - integral_a^b f(z(t)) z'(t) dif t \
                                  &= - integral_gamma f(z) dif z
  $
]

In many proofs, it is useful to find an upper bound for the quantity $abs(integral_gamma f(z) dif z)$.
Intuitively, it should be bounded by the maximum value of $abs(f(z))$ on $gamma$ times
the length of $gamma$.

#proposition(
  title: [ML Inequality],
)[
  Let $f$ be a continuous function defined on a curve $gamma$. Then
  $
    abs(integral_gamma f(z) dif z) <= max_(z in gamma) abs(f(z)) len(gamma)
  $<eq:16>
]

Inequality @eq:16 is known as the #index(entry: [ML inequality])[ML inequality],
in which _M_ and _L_ stand for the _Maximum_ _Modulus_ of $f$ on $gamma$ and the _Length_ of $gamma$,
respectively.

#proof[
  We will first prove the proposition for the case that $gamma$ is smooth, and
  then extend it to the case that $gamma$ is piecewise smooth.

  *Proof for the Smooth Curves:*
  Assume $gamma$ is smooth. Let $gamma = z(t), space t in [a, b]$. Then we have
  $
    abs(integral_gamma f(z) dif z) &= abs(integral_a^b f(z(t)) z'(t) dif t) \
                                   &<= integral_a^b abs(f(z(t))) abs(z'(t)) dif t
  $<eq:15>
  Because and $abs(f(z(t)))$ a real-valued continuous function on $[a, b]$ and $[a, b]$ is
  compact, by @thm:5, $abs(f(z(t)))$ attains its maximum value $M = max_(t in [a, b]) abs(f(z(t)))$ on $[a, b]$.
  Applying the same argument to $abs(f(z))$ on $gamma$, we find that $abs(f(z))$ attains
  its maximum value $M' = max_(z in gamma) abs(f(z))$ on $gamma$. In fact, $M = M'$.

  Then the right-hand side of @eq:15 can be further bounded by
  $
    integral_a^b abs(f(z(t))) abs(z'(t)) dif t &<= integral_a^b M abs(z'(t)) dif t \
                                               &= M integral_a^b abs(z'(t)) dif t \
                                               &= M len(gamma)
                                               &"by definition of length of a curve"
  $
  This proves the proposition for smooth curves.

  *Proof for the Piecewise Smooth Curves:* Suppose $gamma = gamma_1 + dots.c + gamma_n$ where
  each $gamma_j$ is smooth. Then
  $
    abs(integral_gamma f(z) dif z) &= abs(integral_(gamma_1 + dots.c + gamma_n) f(z) dif z) \
                                   &= abs(integral_(gamma_1) f(z) dif z + dots.c + integral_(gamma_n) f(z) dif z) \
                                   &<= abs(integral_(gamma_1) f(z) dif z) + dots.c + abs(integral_(gamma_n) f(z) dif z) \
                                   &"Apply the ML inequality to each smooth piece" \
                                   &<= max_(z in gamma_1) abs(f(z)) len(gamma_1) + dots.c + max_(z in gamma_n) abs(f(z)) len(gamma_n) \
                                   &"Pick the greatest value among all max's"\
                                   &= max_(z in gamma) abs(f(z)) (len(gamma_1) + dots.c + len(gamma_n) )\
                                   &= max_(z in gamma) abs(f(z)) len(gamma)
  $
]

A #index[primitive] for $f$ in an open set $Omega$ is a function $F$ such that $F$ is
holomorphic in $Omega$ and $F'(z) = f(z) space forall z in Omega$. This term is
an analogy to the antiderivative for real functions.

#theorem(
  title: [Second Fundamental Theorem of Calculus],
)[
  Suppose $f: [a, b] -> RR$ is Riemann integrable on $[a, b]$. Let function $F$ be
  defined on $[a, b]$ such that its derivate $F'$ exists in $(a, b)$ and
  $
    F'(x) = f(x) quad forall x in (a, b)
  $
  Moreover, we assume at the endpoints $a$ and $b$, the one-sided derivatives of $F$, $F(a+)$ and $F(b-)$,
  both exist (as finite numbers). Then we have
  $
    integral_a^b f(x) dif x = F(b-) - F(a+)
  $<eq:18>
]<thm:6>

Equation @eq:18 might not be the one the reader might be familiar with. The
usual one is
$
  integral_a^b f(x) dif x = F(b) - F(a)
$
We will use the following example to show why we need to consider the one-sided
limits of $F$.

#example[
  Let
  $
    f(x) = cases(2x sin(1/x) - cos(1/x) quad &x != 0, 0 &x = 0) space, quad x in [0, 2/pi]
  $
  and
  $
    F(x) = cases(x^2 sin(1/x) quad &x != 0, c &x = 0) space, quad x in [0, 2/pi]
  $
  where $c$ is some constant. Note that $F'(x) = f(x) space forall x in (0, 2/pi)$.
  Hence, by @thm:6, we have
  $
    integral_0^(2/pi) f(x) dif x = F(2/pi-) - F(0+) = F(2/pi) - F(0+) = 4/pi^2 - 0 = 4/pi^2
  $
  In fact, the value $F(0) = c$ does not affect the integral since in the
  computation, we used the right-hand limit $F(0+)$ instead of $F(0)$.
]

#theorem(
  title: [Second Fundamental Theorem of Calculus for Contour Integration],
)[
  Suppose $f: Omega -> CC$ is continuous and has a primitive $F$ in $Omega$. Let $gamma$ be
  a curve in $Omega$ that starts at $z_0$ and ends at $z_1$. Then
  $
    integral_gamma f(z) dif z = F(z_1) - F(z_0)
  $
]<thm:7>

#proof[
  As usual, we first prove the theorem assuming $gamma$ is smooth, and then extend
  it piecewise smooth curves.

  *Proof for the Smooth Curves:* Let $gamma = z(t), space t in [a, b]$. The
  function $F(z(t))$ has a derivate on $[a, b]$ by the chain rule since $z$ is
  differentiable on $[a, b]$, and $F$ is holomorphic ar each point $z(t)$.
  Moreover, the derivative of $F(z(t))$ is given by
  $
    dif / (dif t) F(z(t)) = F'(z(t)) z'(t) = f(z(t)) z'(t)
  $<eq:17>
  Note that $f(z(t)) z'(t)$ is continuous on $[a, b]$. Consequently, both its real
  and imaginary parts are also continuous, and hence Riemann integrable on $[a, b]$.
  Notice also that since the functions involved in @eq:17 are functions of a real
  variable $t$, we have
  $
    Re[f(z(t)) z'(t)] &= Re[ dif / (dif t) F(z(t)) ] = dif / (dif t) Re[F(z(t))]\
    Im[f(z(t)) z'(t)] &= Im[ dif / (dif t) F(z(t)) ] = dif / (dif t) Im[F(z(t))]
  $

  Then, we may apply @thm:6 to both $Re[f(z(t)) z'(t)]$ and $Im[f(z(t)) z'(t)]$:
  $
    integral_a^b Re[f(z(t)) z'(t)] dif t &= Re[F(z(b))] - Re[F(z(a))]
    = Re[F(z_1) - F(z_0)] \
    integral_a^b Im[f(z(t)) z'(t)] dif t &= Im[F(z(b))] - Im[F(z(a))]
    = Im[F(z_1) - F(z_0)]
  $
  Adding the two equations above, we obtain
  $
    integral_gamma f(z) dif z = integral_a^b f(z(t)) z'(t) dif t = F(z_1) - F(z_0)
  $

  *Proof for the Piecewise Smooth Curves:* Suppose $gamma = gamma_1 + dots.c + gamma_n$ where
  each $gamma_j$ is smooth, and $gamma_j$ starts at $w_(j-1)$ and ends at $w_j$ ($w_0 = z_0$ and $w_n = z_1$).
  Then
  $
    integral_gamma f(z) dif z &= integral_(gamma_1) f(z) dif z + dots.c + integral_(gamma_n) f(z) dif z \
                              &"Apply this theorem to each smooth piece" \
                              &= sum_(j=1)^n (F(w_j) - F(w_(j-1))) \
                              &= F(w_n) - F(w_0)\
                              &= F(z_1) - F(z_0)
  $
]

An immediate consequence of @thm:7 is that if $gamma$ is a closed curve, then
the contour integral will be zero.

#corollary[
  Let $f: Omega -> CC$ be a continuous function that has a primitive $F$ in $Omega$.
  If a curve $gamma$ in $Omega$ is closed, then
  $
    integral_gamma f(z) dif z = 0
  $
]<cor:2>

#proof[
  Let $gamma$ be parameterized by $z: [a, b] -> CC$ ($z(a) = z(b)$). (Note that $z(t)$ is
  not necessarily continuously differentiable on $[a, b]$ since $gamma$ may be
  only piecewise smooth.) We can split $gamma$ into two pieces. Let $alpha = z(t), space t in [a, (a+b)/2]$ and $beta = z(t), space t in [(a+b)/2, b]$.
  Suppose $z_0 = z(a) = z(b)$ and $z_1 = z((a+b)/2)$. We have $gamma = alpha + beta$.
  Note that curves $alpha$ and $beta^-$ both start at $z_0$ and end at $z_1$.
  Therefore, by @thm:7, we have
  $
    integral_gamma f(z) dif z &= integral_alpha f(z) dif z + integral_beta f(z) dif z \
                              &= integral_alpha f(z) dif z - integral_(beta^-) f(z) dif z \
                              &= (F(z_1) - F(z_0)) - (F(z_1) - F(z_0)) \
                              &= 0
  $
]

#corollary[
  If $f$ is holomorphic in a connected open set $Omega$ and $f' = 0$, then $f$ is
  constant.
]

#proof[
  Pick a point $z_0 in Omega$. Because $Omega$ is connected, by @thm:8, there
  exits a curve $gamma$ from $z_0$ to $z$ for any $z in Omega$. Since $f' = 0$ is
  continuous, and $f$ is its primitive, @thm:7 is applicable. Integrating $f'$ along $gamma$,
  we have
  $
    integral_gamma f'(z) dif z = f(z) - f(z_0)
  $
  Meanwhile,
  $
    integral_gamma f'(z) dif z = integral_a^b f'(z) z'(t) dif t
    = integral_a^b 0 dot z'(t) dif t
    = 0
  $
  Therefore, $f(z) = f(z_0)$ for all $z in Omega$. This proves $f$ is constant.
]

= Cauchy's Theorem and Its Applications

== Goursat's Theorem

Recall in previous chapter, we have seen in @cor:2 that if $f$ has a primitive
in an open set containing a closed curve $gamma$, then
$
  integral_gamma f(z) dif z = 0
$
Now, assuming $f$ is holomorphic, we want to show that $f$ has a primitive in
some open set, and hence conclude that the integral of $f$ along any closed
curve in that open set is zero. We shall start from #index[Goursat's theorem].

#theorem(
  title: [Goursat's Theorem],
)[
  Let $Omega subset.eq CC$ be a open set and $T subset.eq Omega$ a triangle whose
  interior is also contained in $Omega$. If $f$ is holomorphic in $Omega$, then
  $
    integral_T f(z) dif z = 0
  $
]<thm:9>

We could state and prove Goursat's Theorem considering the counter integral
along a rectangle. But we will see in @cor:3 that the rectangle version is an
immediate corollary of this triangle version since we can divide a rectangle
into two triangles.

#proof[
  Let $T^(0)$ denote the original triangle $T$, and let $d_0$ and $p_0$ denote the
  diameter and perimeter of $T^(0)$, respectively. We will divide this triangle
  into four smaller triangles, $T^(1)_1$, $T^(1)_2$, $T^(1)_3$, and $T^(1)_4$.
  This is done by bisecting each side of $T^(0)$, and then connecting the
  midpoints. The construction is illustrated in @fig:5.

  #figure(
    image("./figures/dividing-into-4-triangles.svg", width: 60%),
    caption: [Dividing triangle $T$ into four smaller triangles.],
  )<fig:5>

  Note that each small triangle $T^(1)_j$ is positively oriented and has half the
  diameter and half the perimeter of $T^(0)$, i.e, $d_1 = 1/2 d_0$ and $p_1 = 1/2 p_0$.
  More importantly, we have
  $
    integral_(T^(0)) f(z) dif z = sum_(j=1)^4 integral_(T^(1)_j) f(z) dif z
  $<eq:19>
  In the big picture, we want to estimate an upper bound of the modulus of the
  contour integral on the left-hand side of @eq:19. And then we will show that
  that upper bound will tend to zero. Taking the modulus on both sides of @eq:19,
  we have
  $
    abs(integral_(T^(0)) f(z) dif z) = abs(sum_(j=1)^4 integral_(T^(1)_j) f(z) dif z)
    <= sum_(j=1)^4 abs(integral_(T^(1)_j) f(z) dif z)
    <= 4 abs(integral_(T^(1)_(j_1)) f(z) dif z)
  $
  where $abs(integral_(T^(1)_(j_1)) f(z) dif z)$ is the maximum value among all
  four moduli of integrals.

  Now, we can further divide the triangle $T^(1)_(j_1)$ in a similar fashion to
  obtain four even smaller triangles, and then further bound the value of $abs(integral_(T^(1)_(j_1)) f(z) dif z)$.
  Repeat this process for $n$ times, we will have a sequence of triangles, ${T^n_(j_n)}$ with
  $
    d_n = 1 / 2^n d_0 quad "and" quad p_n = 1 / 2^n p_0 quad forall n in ZZ^+
  $
  And we have the following inequality:
  $
    abs(integral_(T^(0)) f(z) dif z) <= 4^n abs(integral_(T^n_(j_n)) f(z) dif z)
  $<eq:20>
  We want to show that the right-hand side of @eq:20 tends to zero as $n -> oo$.

  #note[
    It is appealing to apply the ML inequality directly to $integral_(T^n_(j_n)) f(z) dif z$.
    Though the length of the triangle tends to zero, it is still $1/2^n p_0$, which
    is not enough to cancel $4^n$ on the right-hand side of @eq:20. Hence, we need
    to further exploit the fact that $f$ is holomorphic by estimating $f(z)$ about
    some point $z_0$.
  ]

  Let $cal(T)^n$ denote solid the union of the triangle $T^n$ and its interior. In
  other words, it is the solid triangle. Clearly we have
  $
    cal(T^0) supset.eq cal(T^1) supset.eq dots.c supset.eq cal(T^n) supset.eq dots.c
  $
  and the diameter $diam cal(T)^n = diam T^n = d_n$ tends to zero as $n -> oo$ since $d_n = 1 / 2^n d_0$.
  Therefore, by @cor:1, these solid triangles intersect at a single point, say $z_0$,
  i.e, $sect.big_(n=0)^oo cal(T^n) = {z_0}$.

  We now estimate $f(z)$ about point $z_0$. Because $f$ is holomorphic at $z_0$,
  we can write
  $
    f(z) = f(z_0) + f'(z_0) (z - z_0) + psi(z) (z - z_0), quad z != z_0
  $<eq:21>
  where $psi(z)$ is a continuous function, and
  $
    lim_(z -> z_0) psi(z) = 0
  $
  Observe the right-hand side of @eq:21. We note that the function defined by the
  sum of the first two term
  $
    g(z) = f(z_0) + f'(z_0) (z - z_0)
  $
  has a primitive
  $
    G(z) = f(z_0) (z - z_0) + 1/2 f'(z_0) (z - z_0)^2
  $
  Therefore, by @thm:7, the contour integral of $g$ along the triangle $T^n_(j_n)$ is
  zero. It then follows that
  $
    integral_(T^n_(j_n)) f(z_0) dif z &= integral_(T^n_(j_n)) f(z_0) + f'(z_0) (z - z_0) + psi(z) (z - z_0) dif z \
                                      &= integral_(T^n_(j_n)) f(z_0) + f'(z_0) (z - z_0) dif z + integral_(T^n_(j_n)) psi(z) (z - z_0) dif z \
                                      &= integral_(T^n_(j_n)) psi(z) (z - z_0) dif z \
  $<eq:22>
  Applying the ML inequality to the last integral, we have
  $
    abs(integral_(T^n_(j_n)) psi(z) (z - z_0) dif z)
      &<= max_(z in T^n_(j_n)) abs(psi(z)(z - z_0)) p_n \
      &"Note that" abs(z - z_0) <= d_n space forall z in T^n_(j_n) \
      &<= max_(z in T^n_(j_n)) abs(psi(z)) d_n p_n \
      &"To ease the notation, let" epsilon_n = max_(z in T^n_(j_n)) abs(psi(z)) \
      &= epsilon_n d_n p_n \
      &= 1/4^n epsilon_n d_0 p_0
  $<eq:23>

  Combining @eq:20, @eq:22, and @eq:23, we have
  $
    abs(integral_(T) f(z) dif z) <= 4^n abs(integral_(T^n_(j_n)) f(z) dif z) <= epsilon_n d_0 p_0
  $<eq:24>
  Since $psi(z) -> 0$ as $z -> z_0$, we have $epsilon_n -> 0$ as $n -> oo$. Let $n -> oo$ at
  both sides of @eq:24, we have $integral_(T) f(z) dif z = 0$. This completes the
  proof.
]

#corollary[
  If $f$ is holomorphic in an open set $Omega$ containing a rectangle $R$ and its
  interior, then
  $
    integral_R f(z) dif z = 0
  $
]<cor:3>

#proof[
  We can split the rectangle $R$ into two triangles $T_1$ and $T_2$ by drawing a
  diagonal. See @fig:6 for the illustration.

  #figure(
    image("./figures/dividing-a-rectangle-into-2-triangles.svg", width: 60%),
    caption: [Dividing rectangle $R$ into two triangles.],
  )<fig:6>

  Then applying @thm:9 to each triangle, we have
  $
    integral_R f(z) dif z = integral_(T_1) f(z) dif z + integral_(T_2) f(z) dif z = 0
  $
]

== Local Existence of Primitives and Cauchy's Theorem in a Disk

#theorem[
  If $f$ is holomorphic in an open disk $D subset.eq CC$, then $f$ has a primitive
  there.
]

#proof[
  Without loss of generality, we may assume the disk $D$ is centered at the
  origin. If it is centered at $z_0$, we can translate the disk to the origin and
  define $tilde(f)(z) = f(z + z_0)$. Then we find a primitive for $tilde(f)$, say $tilde(F)$.
  The primitive for $f$ is then given by $F(z) = tilde(F)(z - z_0)$.

  Assume $D$ is centered at the origin, we are going to construct a primitive $F$ for $f$ in $D$ using
  a contour integral. For any point $z in D$, curve $gamma_z$ is taken to be the
  horizontal line segment from $0$ to $Re z$ followed by the vertical segment from $Re z$ to $z$.
  Note that $gamma_z$ is indeed contained in $D$. Let function $F$ be defined by
  $
    F(z) = integral_(gamma_z) f(w) dif w
  $
  We will show $F$ is indeed a primitive for $f$ in $D$. Hence, we need to
  estimate the quotient $(F(z+h) - F(z)) / h$ when $h -> 0$.

  This invites us to consider the contour integral of $f$ along curve $gamma_(z_h) - gamma_z$.
  As illustrated in @fig:7, by adding a rectangle and a triangle without change
  the value of the contour integral due to @thm:9 and cor:3, one may verify that
  $
    F(z+h) - F(z)
    = integral_(gamma_(z+h) - gamma_z) f(w) dif w
    = integral_eta f(w) dif w
  $<eq:25>
  where $eta$ is the line segment from $z$ to $z+h$.

  #figure(
    image("./figures/adding-a-rectangle-and-a-triangle.svg", width: 60%),
    caption: [
      Construction of curve $eta$ by adding a rectangle and a triangle to the curve $gamma_(z+h) - gamma_z$.
    ],
  )<fig:7>

  Now, we are going to estimate $f(w)$ about the point $z$. Because $f$ is
  continuous, we can write
  $
    f(w) = f(z) + psi(w), quad w in D without {z}
  $
  where $psi(w)$ is continuous and
  $
    lim_(w -> z) psi(w) = 0
  $
  It then follows that
  $
    integral_eta f(w) dif w
      &= integral_eta f(z) + psi(w) dif w \
      &= f(z) integral_eta 1 dif w + integral_eta psi(w) dif w \
      &= f(z) h + integral_eta psi(w) dif w
  $<eq:26>
  Combining @eq:25 and @eq:26, we have
  $
    abs((F(z+h) - F(z)) / h - f(z))
      &= 1 / abs(h) abs(integral_eta psi(w) dif w)\
      &"Apply the ML inequality"\
      &<= 1 / abs(h) max_(w in eta) abs(psi(w)) abs(h)\
      &= max_(w in eta) abs(psi(w))
  $<eq:27>
  As $h -> 0$, we have $w -> z$ and hence $psi(w) -> 0$. Therefore, the limit of
  the right-hand side of @eq:27 is $0$ as $h -> 0$. This proves $F'(z) = f(z)$.
]

// References
#bibliography("complex-analysis.bib", title: "References")

// Indices
#index-page()