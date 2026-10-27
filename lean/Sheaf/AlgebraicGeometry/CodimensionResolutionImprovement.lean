module

public import Sheaf.AlgebraicGeometry.CodimensionResolutionPrefix
public import Sheaf.AlgebraicGeometry.SmallSingularLocusResolution
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.BlowupUniversal
import WeilConjectures.Blowup.Proper

/-! # Compatible finite codimension resolution approximations

Source: Temkin, Non-embedded Desingularization, §§4.1.1–4.1.5 and 4.3,
printed pp.26–31 (blueprint: lem-per-codimension-resolution-improvement).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- From a fixed small-singular-locus rule one can construct compatible finite prefixes
of ordinary resolution rules, resolving successively through every finite codimension.
Each constructed prefix has a successor retaining all earlier rules. No stabilization,
global resolution, or extension of an arbitrary admissible prefix is asserted.
Source: Temkin §§4.1.1–4.1.5 and 4.3, before Lemma 4.1.3(ii)
(blueprint: lem-per-codimension-resolution-improvement).

Proof:
1. We construct rules by induction on $d$, simultaneously retaining the stronger invariant that
every center is supported over $X_{\mathrm{sing}}$. Start with $R_0(X)$ empty. A height-zero local
ring of a reduced Noetherian scheme is a field (its maximal ideal is its nilradical), so
$T_0(X)=X_{\mathrm{sing}}$ misses $X^{\le0}$ and is closed by
[lem-per-regular-pullback-unresolved-strata]. The empty tower is preserved under every pullback.
At every later stage this same cited closedness assertion applies. The induction below only calls
already defined rules $R_i$ with $i\le d$ on further objects, so it does not change any earlier
rule. Dependencies: lem-per-regular-pullback-unresolved-strata.
2. Suppose the rules through $d$ are constructed, and set $r=d+1$, $f=R_d(X)$ and $Z=T_d(X)$. By
[lem-per-regular-pullback-unresolved-strata], the height-$r$ points of $Z$ form a finite set $S$
of generic points. If $S$ is empty set $R_r(X)=f$. Otherwise let $C=\overline S_{\mathrm{red}}$
and $U=X\setminus C$. The set $C$ lies in $Z$, has pure codimension $r$, and its local scheme at
each $s\in S$ is $\operatorname{Spec}\kappa(s)$; hence $C$ is regular at these points. Insert
$\operatorname{Bl}_C(X)\to X$ at the start of $f$ using [lem-per-blowup-sequence-insertion]. Each
old center has image of pure codimension at most $d$, so its generic image points avoid $C$; its
assumed schematic density over those points makes it the closure of its restriction over $U$. This
verifies the insertion hypothesis. Every old replacement retains its reduced structure, pure image
codimension and schematic density, by the same node. Dependencies:
lem-per-regular-pullback-unresolved-strata, lem-per-blowup-sequence-insertion.
3. The pullback of the ideal of $C$ to the new first stage is an effective Cartier ideal by
[thm-nagata-blowup-principalizes-center], and it stays so through every subsequent blowup by
[lemma-nagata-cartier-total-transform-blowup]. All ambient schemes are reduced Noetherian by
[lem-per-blowup-local-dimension-bound]; their local schemes and reduced centers are
quasi-excellent by its last clause. Properness needed for taking images and globalizing follows at
every blowup from [thm-nagata-global-blowup-proper]. Thus all local objects used below belong to
$\mathscr C$. Over $U$ the inserted stages are empty and the old tower, including its ideals, is
unchanged. Over $X^{\le d}$ the same holds, since $C$ has no such points. Dependencies:
thm-nagata-blowup-principalizes-center, lemma-nagata-cartier-total-transform-blowup,
lem-per-blowup-local-dimension-bound, thm-nagata-global-blowup-proper.
4. Process the old centers in their original order, after the new first center. If $W\subset P$ is
the current old center, put $W_S=\coprod_{s\in S}(W\times_X\operatorname{Spec}\mathcal O_{X,s})$.
By [lem-per-blowup-local-dimension-bound], every summand has dimension at most $r-1=d$.
Consequently the already constructed $R_d(W_S)$ is a complete strong resolution: its unresolved
set is disjoint from every point. Moreover $W_S$ is regular away from its closed base fibres: at a
proper generalization of $s$ the image has height less than $r$, where the old tower was already
strongly resolved and all our insertions are empty. By the stronger inductive invariant, every
center of $R_d(W_S)$ is therefore supported over those closed fibres. Apply
[lem-per-local-blowup-tower-globalization] with $P=W$ to its synchronized centers, blowing them up
in the ambient scheme containing $W$. Its conclusion identifies the local strict transforms with
the terminal scheme of $R_d(W_S)$, so the new strict transform of $W$ is regular over every $s\in
S$. The inserted centers themselves are regular there. Each global new center is reduced, nowhere
dense and equicodimensional over $X$ of codimension $r$. Dependencies:
lem-per-blowup-local-dimension-bound, lem-per-local-blowup-tower-globalization.
5. Insert the ambient correction just obtained before the blowup in $W$, using
[lem-per-blowup-sequence-insertion]. Its first replaced center is precisely the strict transform
of $W$ just resolved locally. Every still-later old center is schematically dense away from $C$,
because its generic image codimension is at most $d<r$, so the remaining insertion hypotheses
hold. The previous old centers and previous inserted centers occur before this correction and are
unchanged. There are only finitely many original centers; processing each exactly once therefore
ends with a finite tower all of whose centers are regular over $X^{\le r}$. All correction centers
lie over $C\subset Z$; they lie over $X_{\mathrm{sing}}$ as well, since by the stronger invariant
$f$ is the identity over $X_{\mathrm{reg}}$, whence $Z\subset X_{\mathrm{sing}}$. This preserves
singular support. It also shows that these corrections are empty on $X\setminus Z$. Dependencies:
lem-per-blowup-sequence-insertion.
6. Let $P$ be the terminal scheme after these corrections. For $s\in S$ put
$P_s=P\times_X\operatorname{Spec}\mathcal O_{X,s}$ and let $D_s$ be the scheme-theoretic inverse
image of the reduced point $s$. It is an effective Cartier divisor by the persistence of the ideal
of $C$ proved above. Since $P\to X$ is proper and of finite type, $D_s$ is of finite type over
$\kappa(s)$, a characteristic-zero field. The singular locus of $P_s$ is contained in $D_s$:
outside the closed fibre the image has height at most $d$ and all modifications made there are the
old, already resolved tower. Apply the given rule of [lem-per-small-singular-locus-resolution]
once to the finite disjoint union $(\coprod P_s,\coprod D_s)$. This gives one finite ordered list
of regular centers and a regular terminal scheme on each component, with synchronizing empty
stages allowed. Each center is supported over the closed fibres, because that rule supports
centers over the singular locus. All its hypotheses, including reducedness and quasi-excellence,
were verified above. Dependencies: lem-per-small-singular-locus-resolution.
7. Append the globalization of this last tower to $P$, using
[lem-per-local-blowup-tower-globalization]. Call the resulting tower $R_r(X)$. Its new centers
have pure $X$-codimension $r$, are reduced and nowhere dense, and are schematically dense over
their generic image points. The local centers and terminal scheme are regular over all $s\in S$.
Outside $C$ the new stages are empty. Thus the terminal scheme and every center are regular over
all of $X^{\le r}$: over a height-$r$ point not in $Z$ the old tower was already resolved; the
only height-$r$ points of $C$ are $S$; lower heights are unaffected. Closedness from
[lem-per-regular-pullback-unresolved-strata] now gives $T_r(X)\cap X^{\le r}=\varnothing$. All new
centers lie over $C\subset Z$ and therefore the old tower is unchanged, with its ordered ideals,
over $X\setminus Z$. Dependencies: lem-per-local-blowup-tower-globalization,
lem-per-regular-pullback-unresolved-strata.
8. Let $h:Y\to X$ be regular. By [lem-per-regular-pullback-unresolved-strata], the selected finite
set for $Y$ consists of the generic points above $S$, and its reduced closure is exactly
$C\times_XY$; the local maps at these points are regular. This proves compatibility of the first
blowup. At each old center, its local disjoint union on $Y$ maps regularly to the local disjoint
union on $X$. Inductive functoriality of $R_d$ gives the same synchronized correction list after
pullback and deletion of empty centers. Globalization and insertion commute with flat base change
by [lem-per-local-blowup-tower-globalization] and [lem-per-blowup-sequence-insertion]. At the
terminal correction the local maps are regular in the cited pair category: they are flat with
geometrically regular fibres, so their fibres remain regular after each finite extension of a
target residue field. The divisor is the schematic pullback of the same ideal of $C$. Thus these
are morphisms of $\mathscr P$, and functoriality of the given $H$ in
[lem-per-small-singular-locus-resolution] applies. It yields the same conclusion for the final
list. An old center that disappears has an empty local correction too; its whole block disappears.
These observations preserve the original relative order of every surviving ideal. They also cover
the case where the selected set on $Y$ is empty. Hence $R_r(Y)$ is exactly the contracted
scheme-theoretic pullback of $R_r(X)$. Dependencies: lem-per-regular-pullback-unresolved-strata,
lem-per-local-blowup-tower-globalization, lem-per-blowup-sequence-insertion,
lem-per-small-singular-locus-resolution.
9. No stage of this construction changes $R_i$ for $i<r$. At the successor just built every
inserted center has codimension $r$ and lies over $T_d(X)$, and all old centers are recovered off
that set by their closure prescription. Since the tower remains strongly resolved on $X\setminus
T_d(X)$, its unresolved set satisfies $T_r(X)\subseteq T_d(X)$. Iterate these inclusions. For
$e\ge d$, each later inserted center is supported over the corresponding unresolved set, hence
over $T_d(X)$; the same is true of its later strict transforms. The repeated closure replacements
of old centers agree off $T_d(X)$, so $R_e(X)$ restricts there to $R_d(X)$ with only empty centers
removed and all surviving ideals in order. Every center of codimension greater than $d$ was
inserted at one of those later stages, so has the required support. Induction on the natural
numbers, starting at the specified empty rule and using only previously fixed rules and $H$,
defines one compatible sequence. No stabilization or finite bound on $\dim X$ is used.
Dependencies: .
-/
theorem exists_codimensionResolutionConstruction
    (H : SmallSingularLocusResolutionRule.{u}) :
    Nonempty CodimensionResolutionConstruction.{u} := by
  sorry

end AlgebraicGeometry
