+++
id = "thm-a1-curve-perverse-heart"
kind = "theorem"
title = "The perverse t-structure on a smooth curve and its heart"
order = 2747
uses = ["cor-pur-adic-and-rational-smooth-dualizing-complexes", "def-per-perverse-subcategories", "def-per-support-condition", "def-weil-t-structure", "def-wf-middle-extension", "lem-exc-closed-support-triangle", "lem-per-dual-lisse-tensor", "lem-weil-closed-costalk-duality", "lem-weil-heart-short-exact-triangles", "prop-constructible-truncations", "prop-sf-localization-all-stages", "prop-weil-heart-abelian", "rem-dl-a1-conventions", "thm-coef-qbar-verdier"]
+++
In the setting of [def-per-support-condition], let the base field $k$ be
perfect (in the applications $k=k_0=\mathbf F_q$ or its algebraic
closure) and let $X=C$ be a smooth separated $k$-scheme of pure dimension
one, for instance $C=A_0$ or a dense open of it. For $k=k_0$ the objects
may equally be Weil complexes on $C_0$, in the conventions of
[rem-dl-a1-conventions]. All conditions below concern cohomology sheaves,
and the operations used in the proof carry the Weil structure, so the
statements hold verbatim in that case. "Sheaf" means a constructible
$\overline{\mathbf Q}_\ell$-sheaf on $C$ (a Weil sheaf in the Weil case),
that is, an object of the heart of the standard t-structure of
[prop-constructible-truncations]. A sheaf is *punctual* if its support is
a finite set of closed points. Let ${}^pD^{\le0}(C)$ and
${}^pD^{\ge0}(C)$ be the classes of [def-per-perverse-subcategories].

1. (*Description.*) For $K\in D^b_c(C,\overline{\mathbf Q}_\ell)$,
   $$
   \begin{aligned}
   K\in{}^pD^{\le0}(C)&\iff \mathcal H^aK=0\ (a>0)\ \text{and}\
   \mathcal H^0K\ \text{is punctual},\\
   K\in{}^pD^{\ge0}(C)&\iff \mathcal H^aK=0\ (a<-1)\ \text{and}\
   \mathcal H^{-1}K\ \text{has no nonzero punctual subsheaf}.
   \end{aligned}
   $$
2. (*t-structure.*) The pair $\bigl({}^pD^{\le0}(C),{}^pD^{\ge0}(C)\bigr)$
   is a bounded t-structure on $D^b_c(C,\overline{\mathbf Q}_\ell)$ in the
   sense of [def-weil-t-structure]. Its heart
   $$
   \mathrm{Perv}(C):={}^pD^{\le0}(C)\cap{}^pD^{\ge0}(C)
   $$
   (the perverse heart candidate of [def-per-perverse-subcategories]) is
   an abelian category.
3. (*The heart.*) $K\in\mathrm{Perv}(C)$ if and only if
   $\mathcal H^aK=0$ for $a\notin\{-1,0\}$, $\mathcal H^0K$ is punctual,
   and $\mathcal H^{-1}K$ has no nonzero punctual subsheaf.
4. (*Basic objects.*) If $j:U\hookrightarrow C$ is a dense open immersion
   and $\mathcal N$ is a lisse sheaf on $U$, then the middle extension
   $(j_*\mathcal N)[1]$ of [def-wf-middle-extension] lies in
   $\mathrm{Perv}(C)$. If $x$ is a closed point with inclusion $i_x$ and
   $E$ is a sheaf on $x$ (a finite-dimensional continuous
   representation of the Galois group, respectively of the Weil group,
   of $k(x)$), then $i_{x*}E$, placed in degree $0$, lies in
   $\mathrm{Perv}(C)$.
5. (*Exact sequences.*) For $P\in\mathrm{Perv}(C)$ the sequence
   $0\to(\mathcal H^{-1}P)[1]\to P\to(\mathcal H^0P)[0]\to0$ is exact in
   $\mathrm{Perv}(C)$. A short exact sequence $0\to Q\to P\to R\to0$ in
   $\mathrm{Perv}(C)$ gives an exact sequence of sheaves
   $$
   0\to\mathcal H^{-1}Q\to\mathcal H^{-1}P\to\mathcal H^{-1}R
   \to\mathcal H^0Q\to\mathcal H^0P\to\mathcal H^0R\to0 .
   $$

## Proof

*Step 0: two facts about sheaves on a smooth curve.* (i) Let $V$ be a
smooth curve (every component of dimension one) and $\mathcal M$ a lisse
sheaf on $V$. Then $\mathcal M$ has no nonzero punctual subsheaf, and in
particular a punctual lisse sheaf on $V$ is zero. Indeed, let
$\mathcal G\subset\mathcal M$ be supported on a finite set $S$ and let
$s$ be a section of $\mathcal G$ over a connected étale $W\to V$ on which
$\mathcal M$ is constant. Then $s$ vanishes on the complement of the
preimage of $S$, which is dense in $W$. A section of a constant sheaf on
a connected scheme that vanishes on a nonempty open is zero, so $s=0$.
(ii) Every sheaf $\mathcal F$ on $C$ has a largest punctual subsheaf
$\mathcal F_{\mathrm p}$, and $\mathcal F/\mathcal F_{\mathrm p}$ has no
nonzero punctual subsheaf. Choose a dense open $j:U\hookrightarrow C$ on
which $\mathcal F$ is lisse. Its complement $Z$ is a finite set of closed
points, because $C$ has pure dimension one. Put
$\mathcal F_{\mathrm p}:=\ker(\mathcal F\to j_*j^*\mathcal F)$. This
kernel vanishes on $U$, so it is punctual. If $\mathcal G\subset\mathcal F$
is punctual, then $j^*\mathcal G=0$ by (i), so $\mathcal G\subset
\mathcal F_{\mathrm p}$. The quotient embeds in $j_*j^*\mathcal F$. A
section of $j_*\mathcal M$ over $W$ is a section of $\mathcal M$ over
$W\times_CU$, so a punctual subsheaf of $j_*\mathcal M$ restricts to zero
on $U$ and is therefore zero. The same argument shows that $j_*\mathcal M$
has no nonzero punctual subsheaf for any lisse $\mathcal M$ on $U$.

*Step 1: the support condition.* The supports of constructible sheaves on
$C$ have dimension $\le1$. So in [def-per-support-condition] the
inequalities for $i\ge1$ are automatic. For $i=0$ the inequality says that
$\mathcal H^0$ is punctual, and for $i<0$ it says that $\mathcal H^{-i}=0$.
This gives
$$
\operatorname{SuppCon}(N)\iff\mathcal H^aN=0\ (a>0)\ \text{and}\
\mathcal H^0N\ \text{is punctual},
$$
which is the first half of (1). Now fix a dense open $j:U\hookrightarrow C$
on which all $\mathcal H^aN$ are lisse, with finite closed complement
$i:Z\hookrightarrow C$. Stalks at the points of $U$ and of $Z$ detect
vanishing, and a lisse punctual sheaf on $U$ is zero by Step 0(i). Hence
$$
\operatorname{SuppCon}(N)\iff \mathcal H^a(j^*N)=0\ (a\ge0)\ \text{and}\
\mathcal H^a(i^*N)=0\ (a>0).\tag{$*$}
$$

*Step 2: the duals on $U$ and on $Z$.* By [cor-pur-adic-and-rational-smooth-dualizing-complexes],
$\omega_U\cong\overline{\mathbf Q}_\ell(1)[2]$. Restriction to an open
commutes with internal Hom, and $j^*\omega_C=\omega_U$, so
$j^*D_C=D_Uj^*$. For a lisse sheaf $\mathcal L$ on $U$,
[lem-per-dual-lisse-tensor] with $K=\overline{\mathbf Q}_\ell$ gives
$D_U\mathcal L\cong\omega_U\otimes\mathcal L^\vee=\mathcal L^\vee(1)[2]$.
Now let $M$ have lisse cohomology sheaves on $U$. Induction on the number
of nonzero cohomology sheaves, using the truncation triangles
$\tau^{\le n-1}M\to M\to\mathcal H^nM[-n]\to$ of
[prop-constructible-truncations] and the exactness of $D_U$, gives
$$
\mathcal H^a(D_UM)\cong\bigl(\mathcal H^{-2-a}M\bigr)^\vee(1),
$$
and these sheaves are again lisse. The reduced scheme $Z$ is a finite
disjoint union of spectra of perfect fields, hence smooth of dimension
zero, so $\omega_Z=\overline{\mathbf Q}_\ell$ by
[cor-pur-adic-and-rational-smooth-dualizing-complexes]. Sheaves on $Z$ are finite-dimensional
representations, and $R\mathcal Hom(-,\overline{\mathbf Q}_\ell)$ is
computed on geometric stalks by the exact linear dual. Hence
$\mathcal H^a(D_ZM)\cong(\mathcal H^{-a}M)^\vee$.

*Step 3: the cosupport condition.* Let $K\in D^b_c(C,\overline{\mathbf Q}_\ell)$,
and choose $U$ and $Z$ as in Step 1 for $K$. By Step 2 this choice also
serves for $N:=D_CK$ on $U$. By [lem-weil-closed-costalk-duality] applied
to $D_CK$, and by the biduality of [thm-coef-qbar-verdier] on $C$ and on
$Z$, we get $Ri^!K\cong Ri^!D_CD_CK\cong D_Zi^*D_CK$, hence
$i^*D_CK\cong D_ZRi^!K$. The object $Ri^!=D_Zi^*D_C$ is constructible by
[thm-coef-qbar-verdier]. By $(*)$ and Step 2,
$$
\operatorname{CosuppCon}(K)\iff
\text{(a) }\mathcal H^b(j^*K)=0\ (b\le-2)\ \text{and (b) }
\mathcal H^b(Ri^!K)=0\ (b<0).
$$
Assume (a). The closed-support triangle, [prop-sf-localization-all-stages]
(on the $\overline{\mathbf Q}_\ell$-category, with Weil-equivariant arrows in the Weil case;
at each finite stage it is [lem-exc-closed-support-triangle]), with $Rj_*j^*K$ constructible,
reads
$$
i_*Ri^!K\to K\to Rj_*j^*K\to .
$$
Since $j^*K\in D^{\ge-1}$ and $j_*$ is left exact, $Rj_*j^*K\in D^{\ge-1}$
and $\mathcal H^{-1}(Rj_*j^*K)=j_*j^*\mathcal H^{-1}K$. Apply the exact
functor $i^*$ (note $i^*i_*=\mathrm{id}$) to the long exact sequence of
cohomology sheaves. This gives $\mathcal H^b(Ri^!K)\cong i^*\mathcal H^bK$
for $b\le-2$, and
$$
0\to\mathcal H^{-1}(Ri^!K)\to i^*\mathcal H^{-1}K\to
i^*j_*j^*\mathcal H^{-1}K .
$$
The second map is $i^*$ of the unit $\mathcal H^{-1}K\to j_*j^*\mathcal
H^{-1}K$. That unit is an isomorphism on $U$, so its kernel is
$i_*\mathcal H^{-1}(Ri^!K)$, which is the largest punctual subsheaf of
$\mathcal H^{-1}K$ by Step 0(ii). So under (a), condition (b) says that
$\mathcal H^bK$ vanishes on $Z$ for $b\le-2$ and that $\mathcal H^{-1}K$
has no nonzero punctual subsheaf. Together with (a) on $U$, this is the
second half of (1).

*Step 4: t-structure.* Write ${}^pD^{\le n}$ and ${}^pD^{\ge n}$ for the
shifts of [def-per-perverse-subcategories]. By (1),
$B\in{}^pD^{\ge1}(C)$ if and only if $\mathcal H^bB=0$ for $b<0$ and
$\mathcal H^0B$ has no nonzero punctual subsheaf. Both classes are
strictly full, and the stability under shifts in axiom 1 of
[def-weil-t-structure] can be read off (1).

For axiom 2, let $A\in{}^pD^{\le0}$ and $B\in{}^pD^{\ge1}$. Then $A$ is in
standard degrees $\le0$ and $B$ in standard degrees $\ge0$. The truncation
axioms of the standard t-structure of [prop-constructible-truncations]
give $\operatorname{Hom}(A,B)=\operatorname{Hom}(\tau^{\ge0}A,B)
=\operatorname{Hom}(\mathcal H^0A,\tau^{\le0}B)=
\operatorname{Hom}(\mathcal H^0A,\mathcal H^0B)$, a Hom of sheaves. The
image of a map $\mathcal H^0A\to\mathcal H^0B$ is a punctual subsheaf of
$\mathcal H^0B$, hence zero.

For axiom 3, let $K$ be given, put $K'=\tau^{\le0}K$ and
$\mathcal F=\mathcal H^0K$, and let $\mathcal F_{\mathrm p}$ be as in
Step 0(ii). Complete the composite
$K'\to\mathcal F[0]\to(\mathcal F/\mathcal F_{\mathrm p})[0]$ to a
triangle $A\to K'\to(\mathcal F/\mathcal F_{\mathrm p})[0]\to$. Its long
exact sequence gives $\mathcal H^aA=\mathcal H^aK$ for $a<0$,
$\mathcal H^0A=\mathcal F_{\mathrm p}$ and $\mathcal H^aA=0$ for $a>0$.
So $A\in{}^pD^{\le0}$. The octahedral axiom applied to
$A\to K'\to K$ gives a triangle $A\to K\to B\to$, together with a triangle
$(\mathcal F/\mathcal F_{\mathrm p})[0]\to B\to\tau^{\ge1}K\to$. Then
$\mathcal H^bB=0$ for $b<0$ and
$\mathcal H^0B=\mathcal F/\mathcal F_{\mathrm p}$, which has no punctual
subsheaf by Step 0(ii). So $B\in{}^pD^{\ge1}$, which is axiom 3 with
$B=(B[1])[-1]$.

Finally, if $K$ has standard cohomology in degrees $[a,b]$, then (1)
gives $K\in{}^pD^{\le b+1}\cap{}^pD^{\ge a}$, so the t-structure is
bounded. Its heart is abelian by [prop-weil-heart-abelian]. This proves
(2), and (3) is the intersection of the two conditions in (1).

*Step 5: basic objects.* $(j_*\mathcal N)[1]$ has only
$\mathcal H^{-1}=j_*\mathcal N$, which has no nonzero punctual subsheaf
by Step 0(ii). $i_{x*}E$ has only $\mathcal H^0=i_{x*}E$, which is
punctual. By (3) both lie in the heart, which is (4).

*Step 6: exact sequences.* In the heart of a t-structure, a sequence
$0\to Q\to P\to R\to0$ is short exact exactly when it extends to a
distinguished triangle $Q\to P\to R\to Q[1]$, by part (4) of
[lem-weil-heart-short-exact-triangles]. For $P\in\mathrm{Perv}(C)$
the standard truncation triangle is
$(\mathcal H^{-1}P)[1]\to P\to(\mathcal H^0P)[0]\to$. Its outer terms lie
in the heart by (3), which gives the first claim of (5). For a short exact
sequence in the heart, the long exact cohomology sequence of the
corresponding triangle, together with the vanishing of $\mathcal H^a$ for
$a\notin\{-1,0\}$ on all three terms, gives the displayed six-term
sequence.
