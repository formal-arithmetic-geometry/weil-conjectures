## Worker report

The delivery states `WeilConjectures.PurityFiniteSetting.divisor_class` in
`Sheaf.Paper.PurityDivisorClass`. Its only postponed proof is this theorem, with
the eight-step DAG proof in its docstring. The family structure and five helper definitions contain actual data: the two
identical etale realizations, their relative normalization, the actual comparison
map, and three explicit compatibility predicates. A §1(B) dependency-module
repair is included for `lem-pur-supported-cup-functoriality`, as detailed below.
The local sign is corrected under §1(C), as
required by return H3; see the recorded correction and citer audit below.

`HEq` is heterogeneous equality, not a chosen map or equivalence. It identifies
literally the same class across the published Ext/Hom presentations and across
the provably equal singleton/range support indices. These types are definitionally
equal except the support index, where `Set.range_const` supplies the equality.
For equal types, `HEq` is equivalent to ordinary equality. This presentation
avoids repeated kernel normalization of the full localization and sheaf-module
structures while retaining the actual published maps.

Hypothesis and clause correspondence:

- The finite setting, algebraically closed base field k, ell distinct from its
  characteristic, finite extension E, and arbitrary positive coefficient level n
  are `P : PurityFiniteSetting`; positivity is its `level_pos` field. The scalar
  ring is its existing `Coefficient`, the standard size lift of A_{E,n}.
  `diagonalExponent`, `diagonalExponent_annihilates`, and
  `diagonalExponent_isUnit` specify m=ell^n and its required properties. There is
  no ramification-divisibility hypothesis.
- The separated finite-type k-scheme setting is the structure map b on B and
  the structure map v composed with b on T, each with `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`. The closed immersion makes D a
  separated finite-type k-scheme too, without another hypothesis.
- Smooth T/B of relative dimension d is `(v : T ⟶ B) (d : ℕ)` with
  `[SmoothOfRelativeDimension d v]`; smooth D/B is `[Smooth (i ≫ v)]`.
  The closed subfamily is `(i : D ⟶ T) [IsClosedImmersion i]`.
- Pure codimension one is the exact pointwise Krull dimension formula `hcodim`.
  Cartierness is the conclusion `∃ hI : i.ker.IsInvertible`, never an added
  assumption on this smooth divisor.
- The canonical global class is the family C of etale Ext representatives,
  together with `DivisorEtaleNormalized` and uniqueness `C' = C` among
  normalized families. For every effective Cartier immersion E into T, its
  actual pro-etale class is `divisorProEtale E (C.homClassOf E hE)`.
  `FunctorialCupH true E 2 1` is precisely the published supported-Hom model
  of H^2_E(T,A(1)), by `supported_cohomology_hom`; it is not ordinary cohomology.
- The global construction is fixed by `Etale.SupportedKummerBoundary`: its
  `supportedDivisorSection` is the transpose of the Cartier-ideal inclusion
  into O_T, its line is the actual dual ideal O_T(E), and its specified frame
  on the complement equals that section. Its extension presentation retains
  this trivialization. Its Yoneda product is the relative Kummer connecting
  map, followed by `ordinaryFiniteRootMap`, z ↦ 1 tensor z. The equality after
  scalar forgetting and the integral generator is the scalar-adjunction
  realization of the same class, not an unconstrained comparison.
  `DivisorEtaleClasses.realizes` requires `HEq (C.classOf E hE).hom
  (C.homClassOf E hE)`. Thus `divisorProEtale` applies `functorialCupCompare`
  to the actual Ext.hom, without a conversion chosen from an existence theorem.
  The source comparison is normalized on constants and its target is the
  identical finite root-tensor twist used in the frame definition.
- Every etale neighbourhood is quantified by U, e, `[Etale e]`, without
  quasi-compactness or an open-immersion requirement. Its equation is f, and
  the `ChosenCartesianSquare` identifies V(f) scheme-theoretically with D_U.
  Such a square is the unique pullback identification, not extra geometry.
  The first local heterogeneous equality compares the published
  `functorialCupPullback` directly with
  `-(P.frameBoundary U (e ≫ a) f)`, namely minus boundary(kappa(f)) in
  the fixed Yoneda normalization. The two supported-Hom types are definitionally equal.
- The second local heterogeneous equality is directly with
  `-(P.frameBoundaryProduct U (e ≫ v ≫ b) 1 (fun _ : Fin 1 ↦ f))`.
  Its support is identified with the singleton by `Set.range_const`. This is minus the defining body of `frameClass` at c=1.
  It also works for arbitrary d, without identifying geometric dimension d
  with coefficient level n. Quantification over every equation gives the
  independence already stated by `frameClass_independent`.
- The family C quantifies over every effective Cartier divisor on T, so it
  includes nonsmooth sums. In the addition clause, i1 and i2 have invertible
  Cartier ideals; s has exactly their product ideal (`_hs`). The conclusion
  supplies its Cartier proof `hsum` and the closed-support inclusions a1, a2
  with the required equations over T. Since s is monic, these are the unique
  canonical inclusions. `functorialCupChangeSupport` is the published
  enlargement-of-support map. The equality is in the s-supported group.
  Product ideal means support union (`IdealSheafData.support_mul`), and its
  local equation is f1*f2. No two-element frame is used for addition.
- The final c1 is an etale module Ext representative; α1 is its identical
  supported-cup ordinary-Hom representation, required by `HEq c₁.hom α₁`.
  Its image under the actual `ordinaryFiniteClass` is required by HEq to equal
  `supportedKummerChern`,
  which is explicitly the ordinary Kummer boundary of the frame-torsor
  class of the dual Cartier ideal, followed by the same root coefficient
  morphism at ell^n. The second equality says that the actual pro-etale
  forget-support map equals `functorialCupOrdinaryCompare` of that same α1.
  This fixes exactly the ordinary first Chern class in the node. All uses of
  G_m here are abelian-sheaf uses; no Z/m-module structure is imposed on it.

Dependency declarations read and used (module, names):

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its `Coefficient`,
  `constantEtale`, and `constant`; all fixed field/coefficient data are retained.
- `Sheaf.Paper.PurityConventions`: `coordinateKummer`, `defaultAnnihilator`,
  and the general-exponent roots comparison. The actual frame prescription
  at ell^n is the recorded `PurityFrameKummer.frameKummerEtale`/`frameKummer`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and
  `SmoothOfRelativeDimension`, using independent geometric d.
- `Sheaf.Paper.PurityFrameClass`: `frameClass`, `frameBoundaryProduct`, and
  the supporting coefficient/twist constructions. The singleton product
  calls this existing definition rather than duplicating the construction.
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `IdealSheafData.IsInvertible.isInvertible_dual_toModules`, with the actual
  `Scheme.Modules.dual` and `IdealSheafData.toModules`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: both kernel-of-restriction
  `supportSections` functors and their derived cohomology; the Hom model is
  the exact representation of these functors supplied by the existing node.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded twist
  interface and its publicly reexported finite positive root-tensor twists;
  the finite line here is precisely `frameTwistEtale`/`frameTwist`.
- `Sheaf.Paper.PurityFrameIndependence`: `frameClass_independent` and its
  canonical pullback-support normalization. Independence is asserted here
  by equality for every local equation.
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`:
  `relative_torsor_cohomology`, relative connecting maps, and compatibility
  with forgetting, pullback and coefficients. Its extension model is used by
  the existing `SupportedKummerBoundary` specification.
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`:
  `nonempty_equiv_quotient_torsor`, the canonical
  `picEquivQuotientTorsorGmSheaf`, and `Pic.toCohomologicalPicardGroup`.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`:
  `SupportedKummerBoundary` and `supportedKummerChern`, including their
  actual canonical divisor section and roots coefficient map.
- `Sheaf.Paper.SupportedCupFunctoriality`: `FunctorialCupH`,
  `functorialCupCompare`, `functorialCupPullback`,
  `functorialCupChangeSupport`, `functorialCupForget`, and
  `functorialCupOrdinaryCompare`; each map has the published normalization.
- `Sheaf.Paper.SupportedCohomologyHom`: `supported_cohomology_hom`.

## Dependency modules

The recorded `lem-pur-supported-cup-functoriality` module timed out at the
60-second file-only compile limit while this item was being checked. I copied
its node and supplied the reviewed Q73 interface-preserving repair in
`Sheaf.Paper.SupportedCupFunctoriality`: redundant imports are removed, the comparison functor is made explicit with its existing exact and monoidal instances, and finite-twist/Ext transport helpers are recorded so their public declarations retain the same
signatures and canonical constructions. The item uses only the unchanged
`FunctorialCupH`, `functorialCupCompare`, `functorialCupPullback`,
`functorialCupChangeSupport`, `functorialCupForget`, and
`functorialCupOrdinaryCompare` declarations. The dependency node's statement,
proof, and dependencies are unchanged; only its `lean` record and the required
repair note are supplied here.

The last three already-landed nodes were added to stmt_deps because these
specific published interfaces are used in the signature. The
`lem-pur-supported-cup-functoriality` dependency record is repaired as described
under **Dependency modules**; its statement and proof dependencies are
unchanged. Proof-only imports (`SmoothPairLocalCoordinates`, `PurityRelativeCone`,
`DivisorTorsorBoundarySigns`, the Mathlib Noetherian/dimension-drop results, and
long-exact-sequence naturality) are omitted from this statement-only module;
their declarations are cited in the theorem docstring. No import cycle is
introduced.

Edge cases checked before writing: D empty has unit Cartier ideal, trivial
relative pair and zero divisor class; T empty has zero groups and vacuous
geometric conditions. At d=0, a codimension-one smooth divisor can be empty,
and no positivity condition on d is added. A unit equation has empty support
and zero localization boundary. Repeated divisors and intersecting divisors
are allowed in the product ideal, even when their sum is not smooth. The
zero coefficient ring has zero classes and does not invalidate uniqueness.
Ramified coefficient levels not divisible by e are retained through ell^n.
Etale neighbourhoods can be disconnected and non-quasi-compact. Identity
neighbourhoods and all canonical support identifications are included.

Searches for an exact existing statement:

- msearch leanfinder: `Kummer divisor class in supported cohomology additive
  and forgetting support first Chern class` returned 8 unrelated ideal-class,
  Selmer-group, and cotangent results; no match.
- msearch loogle: `AlgebraicGeometry.Scheme, "Kummer"` returned no hits.
- msearch grep: `divisorClass|firstChern|supportedKummer` returned no Mathlib hits.
- msearch leansearch: `Kummer cycle class of Cartier divisor additive with
  support and maps to first Chern class` returned 8 generic cohomology-class
  and homology functoriality results; no match.
- rg in Mathlib, the upstream `WeilConjectures` tree and side `lean/Sheaf`
  for the new declaration names found no existing declaration.
- Upstream grep for the blueprint id found no statement. Side searches for
  divisorClass, firstChern and the blueprint id found the ordinary supported
  Kummer *specification* and the relative-cone/sign lemmas, which are reused;
  none already states this divisor-class theorem.

Return H3 identifies a sign error that the stage-1 relative-cone extraction
did not resolve: the signed-cone connecting map and the recorded Yoneda product
cannot be substituted for one another in this normalization. Both existing
lemmas remain imported; neither is redefined. The statement correction below
records the change explicitly; no unresolved dispute remains in this item.

Compilation uses only the prescribed scompile.py wrapper, one file at a time.
The initial formulation diagnosed support-index transport and implicit application
of family equality. Kernel diagnostics then identified expensive definitional
conversions between the existing Ext/Hom interfaces. The final structure records
the two identical realizations with HEq, and the local and ordinary comparisons
use HEq at the same interface boundaries. Every canonical map is retained, and
no clause is discarded. The only postponed proof remains `divisor_class`.

## Statement corrected

H3 is repaired in both local HEq clauses, the helper docstring, theorem proof
step 6, and DAG proof steps 3–6. The recorded theorem signature stays verbatim:
the change is in the body of its named local-equation predicate. The new
`statement_change` retains the complete old statement and old proof/dependency
lists and audits all six direct citers. The initial saved-packet dry run passed
at 0f8718a386; mechanical acceptance did not resolve the returned mathematical
fault, so that packet was repaired before pushing. Comparison with the current
base found only the existing packet's `lean` and three added `stmt_deps` fields.

The old statement, retained verbatim in `statement_change.old_statement`, was:

> Fix the finite-coefficient setting of [def-pur-conventions], with $\Lambda=A=A_{E,n}$ and arbitrary $n\geq1$. In the separated finite-type $k$-scheme setting of [sk-def-purity-conv], let $T\to B$ be smooth of relative dimension $d$ and let $D\hookrightarrow T$ be a closed subfamily smooth over $B$, of pure codimension one as in [def-pur-frame-class]. Thus $D$ is an effective Cartier divisor [def-pc-divisor-line-bundle]. There is a canonical Kummer divisor class
> $$\operatorname{cl}(D)\in H^2_D(T_{\mathrm{proet}},A(1))$$
> with supported cohomology as in [def-pur-support-cohomology] and twist as in [def-coefficient-twists-detailed]. It is the global class constructed from the line bundle $\mathcal O_T(D)$ with its canonical section trivializing it on $T\setminus D$, by the relative torsor Kummer connecting map [lem-amb-relative-torsor-cohomology], followed by the coefficient map on roots prescribed in [def-pur-frame-class]. For every etale neighbourhood $U\to T$ on which $D_U$ has equation $f$, its restriction is
> $$\operatorname{cl}(D)|_U=\partial\kappa(f)\in H^2_{D_U}(U,A(1)).$$
> In particular it agrees with the rank-one frame class of [def-pur-frame-class], independently of the equation as in [lem-pur-frame-independence].
> 
> The same relative construction defines $\operatorname{cl}(E)$ for any effective Cartier divisor $E$ on $T$, including a sum of smooth divisors. If $D_1,D_2$ are such divisors and $Z=|D_1|\cup|D_2|$, then, after the canonical enlargement-of-support maps,
> $$\operatorname{cl}(D_1+D_2)=\operatorname{cl}(D_1)+\operatorname{cl}(D_2)\quad\text{in }H^2_Z(T,A(1)).$$
> Here $D_1+D_2$ is defined by the product of the two Cartier ideals, so locally its equation is $f_1f_2$, not the two-element frame $(f_1,f_2)$. Forgetting support sends $\operatorname{cl}(D)$ to $c_1(\mathcal O_T(D))\in H^2(T,A(1))$. Precisely, $c_1(L)$ means the ordinary etale Kummer connecting image of the frame-torsor class of $L$ [lem-sc-line-bundle-torsor], at exponent $m=\ell^n$ killing $A$, mapped to the pro-etale twist by the same coefficient morphism as [def-pur-frame-class]. No $\mathbf Z/m\mathbf Z$-module structure on $\mathbf G_m$ is assumed.

The old local formula was `cl(D)|_U = ∂κ(f)` and claimed agreement with the
rank-one frame class. The corrected formula is `cl(D)|_U = -∂κ(f)`, hence minus
that frame class, in the fixed Yoneda convention of
`def-asd-ordinary-supported-kummer-boundary`. Additivity and the positive
ordinary Chern class are unchanged. The source read was the current
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.md`
and its proof, clause (a) and final forget-support paragraph. Their intended
relative pair and ordinary Chern normalization are retained; the cone-model
positive local formula is translated to the recorded Yoneda construction, as
required by the independent return at 1c8be9c74d60. This is a lemma inside the
unit; neither the recorded affine-line unit statement nor current vector-bundle
unit statement is changed.

Computation checked directly against the declarations:

1. `EtalePicard.etaleIsoTorsorVal_vadd` (in namespace `Scheme.Modules`) gives
   the action `smulMor g ≫ e`. For the dual basis e=1/f the canonical divisor
   section is τ=f·e, as `supportedDivisorSection` transposes the ideal inclusion.
2. Unfolding `SupportedKummerBoundary`, equivariance gives
   F(τ)=a(f)+F(e); its specified-section clause gives F(τ)=0. Thus
   F(e)=-a(f)=a(f⁻¹), writing G_m additively in the middle expression.
3. In the source localization sequence
   0 → j_!Z_W → Z_U → i_*Z_D → 0, the generator one restricts to one on W.
   Its pushout along 1↦f⁻¹ therefore has a lift of one restricting to a(f⁻¹).
   This is precisely F(e) above. The local pushout extension class is the
   negative of the pushout along 1↦f. Compose with the Kummer extClass and
   root map: ∂δ(f⁻¹)=-∂δ(f), and hence the local class is -∂κ(f).
4. `DivisorTorsorBoundarySigns.trivial` instead describes the cone pair (0,g)
   in D(a,b)=(da,res(a)-db); localization is b↦(0,-b). Its `coefficients`
   clause gives the positive cone expression (0,-dr), because the relative
   connecting map anticommutes with localization. This explains the previous
   erroneous positive answer without reassigning the Yoneda normalization.
5. `Sheaf.Torsor.classH1_lifts` in upstream `CategoryTheory/Sites/Torsor.lean`
   says the ordinary lifting torsor has the positive connecting class.
   `Pic.toCohomologicalPicardGroup` in upstream `Sites/GmPicard.lean` is
   explicitly classH1 of Isom(O,L). Pulling back the supported extension
   along Z_T→i_*Z_D has that lifting torsor, so its forgotten class is
   +c1(O(D)). Negating the entire family would break the Chern clause.

A distinguishing edge case is k=algebraic closure of F₂, ell=3, E=Q₃, n=1,
T=A¹_k, D={0}, f=t. The rank-one residue computation gives ∂κ(t) residue 1
in F₃; its negative has residue 2, so the old formula cannot hold. Unit
functions, empty divisors, and characteristic-two coefficient rings can mask
the fault because the boundary vanishes or equals its negative. The correction
keeps all these cases and changes neither the geometric nor coefficient hypotheses.

Citer audit (searched all `dag/nodes` for the exact quoted item id, then kept
exactly those whose `stmt_deps` or `proof_deps` contain it):

- `thm-pur-projective-bundle-formula` — holds: false. Steps 3-4 identify the divisor class with +boundary and its n-fold coordinate product; the Yoneda class has sign - and the product has sign (-1)^n, so those normalization steps need repair.
- `lem-pur-flag-local-comparison` — holds: false. Step 1 identifies +boundary with the normalized Cartier morphism; it is -boundary, so the stated r-fold comparison acquires (-1)^r.
- `thm-pur-rank-one-thom` — holds: false. The isomorphism statement survives multiplication by -1, but step 1 explicitly asserts the positive local equation and must be repaired.
- `lem-pur-cartier-class-agreement` — holds: true. Both constructions use the same frame torsor, specified section and Yoneda supported Kummer extension; its equality and arbitrary-base-change claim survive, with the corrected local sign.
- `thm-pur-localized-top-chern` — holds: false. Step 6 identifies the zero-section divisor class with the class glued from +boundary; the local value is -boundary, so this argument for L1 needs repair.
- `thm-pur-trace-normalization-transitivity` — holds: false. Step 3 uses the divisor theorem to send +boundary to +c1 on the projective line; the corrected theorem sends -boundary to +c1, so the trace-normalization argument needs repair.

The five broken uses are reported for maintainer repair; no citer is edited.
In particular, calling a signed class a generator still proves invertibility,
but it does not preserve a displayed equality or residue normalization.

## Second reading by NE

This is a clause-by-clause self-check of the repaired node and module, not a
claim that a second worker reviewed it. The dispatcher prohibits starting
other agents and assigns independent review to the maintainer. The previous
short reread paragraph was insufficient (H11); the actual reading follows.

- Finite coefficients: the node fixes k, ell, E, arbitrary n≥1 and A_{E,n}.
  The binder `P : PurityFiniteSetting.{u}` retains those data; `level_pos`
  supplies positivity, and `diagonalExponent` is ell^n. None of the local,
  additive or Chern predicates changes n or imposes ramification divisibility.
- Schemes: `B T D : Scheme.{u}`, `b`, and `v ≫ b` represent the separated
  finite-type k-schemes. Both have `IsSeparated`, `LocallyOfFiniteType` and
  `QuasiCompact` hypotheses. There is no additional smoothness of B.
- Smooth pair: `v : T ⟶ B`, independent `d : ℕ`, and
  `[SmoothOfRelativeDimension d v]` match relative dimension d.
  `[IsClosedImmersion i]` and `[Smooth (i ≫ v)]` match the closed smooth
  subfamily. `hcodim` is the pointwise stalk-dimension difference one.
  The theorem concludes `∃ hI : i.ker.IsInvertible`; Cartierness is not assumed.
- Global class: `∃ C : P.DivisorEtaleClasses T` gives each actual Cartier
  divisor an etale Ext class and identical supported-Hom representative.
  `realizes` is HEq with Ext.hom, so the extra representation is determined.
  `divisorProEtale` applies the recorded canonical `functorialCupCompare`.
  `DivisorEtaleNormalized` quantifies over every Cartier immersion and calls
  `Etale.SupportedKummerBoundary`, including the dual ideal, canonical section,
  its zero image, exact extension and Yoneda product. Uniqueness of normalized
  C follows from that specification and scalar adjunction; it does not add
  an arbitrary choice or an extra geometric condition.
- First local clause: `DivisorLocalEquations` quantifies over every U, etale e,
  equation f and Cartesian square identifying V(f) with D_U. It restricts
  the actual class by `functorialCupPullback true`. Its first HEq now has
  right side `-(P.frameBoundary U (e ≫ a) f)`, exactly the corrected minus
  boundary formula. The old positive expression was the mismatch found in H3.
- Rank-one clause: the second HEq now has right side
  `-(P.frameBoundaryProduct U (e ≫ a) 1 (fun _ : Fin 1 ↦ f))`.
  The constant singleton range equals {f}; this is precisely minus the
  existing one-factor frame class with the same support, twist and degree.
  Quantification over every equation retains independence; no identification
  of d with the coefficient level and no quasi-compactness of U is introduced.
- Extension to all Cartier divisors: `C.classOf` and the normalization quantify
  over every i with invertible ideal, including nonsmooth sums. The theorem's
  smooth-pair hypotheses serve to conclude Cartierness of its initial D only.
- Addition: `DivisorAdditive` has invertible ideals for i₁ and i₂ and the exact
  equation `s.ker = i₁.ker * i₂.ker`. Its existential `hsum` concludes
  Cartierness of the sum, while a₁, a₂ and their equations give the unique
  support inclusions. The displayed equality uses `functorialCupChangeSupport`
  on both summands. It uses f₁f₂ locally and never a two-factor frame of the sum.
- Ordinary clause: `DivisorChern` provides c₁ with the same ordinary-Hom α₁
  through `HEq c₁.hom α₁`. Its first comparison uses the actual
  `ordinaryFiniteClass` and positive `supportedKummerChern` of the dual ideal.
  Its last equality applies the canonical forget-support map and ordinary
  site comparison. Both coefficient maps are the same ell^n root map; G_m
  is used only as an abelian sheaf. No local ordinary-H² injectivity is assumed.
- Final source and edge-case check: the repaired equation has the forced
  Yoneda sign, addition is still an equality in the union support, and the
  ordinary class still has positive Picard normalization. Empty schemes,
  empty divisors, d=0, units, intersecting/repeated summands, zero coefficient
  groups, arbitrary etale neighbourhoods, and identity maps remain included.
  Both HEq bodies changed; the theorem signature, seven-declaration list,
  complete binders, and sole postponed theorem remain intact. No new node,
  dependency-module repair, or additional sorry was introduced.

Repair validation: prescribed scompile.py completed cleanly for both its sandbox
check (24.4 s) and library-path check (21.9 s). The delivered module has one
`sorry`, the intended theorem only; no declaration was proved. The recorded
theorem signature equals the source text verbatim, and every Lean line is at
most 100 characters. Delivery preflight and its own per-file compile are also
required before the final push.

## Timeout-return repair validation (2026-10-18)

The return at immutable head 4c33fc20260f reported a 60-second timeout in
`Sheaf.Paper.SupportedCupFunctoriality`. Following the repair-retry brief, I
first retained the saved packet and ran deliver2.py with --no-push. It passed
compilation and server preflight at dry-run commit 0c384720db. The wrapper
encountered a missing overlay artifact for AffineSpaceLinearTraceInvariance
and automatically confirmed compilation against current server sources; the
final result was OK, with no compiler failure or disallowed warning. No
timeout limit was changed and no compiler or delivery script was modified.

The retained dependency module contains the existing interface repair described
above. I reread its canonical comparison functor and exact/monoidal instances,
the selected-site supported Hom model, pullback and closed-support enlargement,
Ext-target transport, and supported/ordinary comparison definitions. They still
use the actual inverse images, normalized coefficient exchanges, finite Tate
lines and degree-zero/shift comparisons. The algebra-law structure retains
identity, composition, concrete Kummer addition and pullback, bilinearity,
associativity, signed symmetry and cup pullback for arbitrary schemes and
closed supports on both sites. The comparison-law structure retains its
bijections, pullback squares, cup and Kummer comparison, forget-support, open
restriction and localization-boundary clauses. The final theorem asserts these
same structures. No new mathematical clause or assumption was added for this
retry; the dependency node still differs from the current base only in lean.

I also reread the divisor-class module and correction record: both local
expressions retain their negative frame boundary, the global class retains
the specified relative torsor normalization, addition uses product ideals and
canonical support enlargement, and forgetting support retains the positive
ordinary Chern normalization. The theorem signature matches lean.statement
verbatim. The correction preserves the current base's old statement verbatim
and audits exactly all six current direct citers. Both Lean files meet the
100-character line limit. The saved Lean modules and node records were
retained unchanged after this successful dry run; this report records the
required self-check and successful validation of the retained repair.
