## Worker report

The module `Sheaf.RingTheory.NilpotentMarkedFreeComplexLift` states
`DerivedCategory.exists_marked_finiteFree_lift_of_nilpotent` with `sorry` as its entire
proof. No definitions, extra nodes, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:

- Commutative ring R and ideal I: `{R : Type u} [CommRing R] (I : Ideal R)`.
- Nilpotence with a positive exponent: `hnil : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = 0`.
- Every element of 1+I is invertible: `hunits : ∀ x : I, IsUnit (1 + (x : R)))`.
- The categories D(R) and D(R/I): the recorded Mathlib `DerivedCategory` on the two
  `ModuleCat` categories, with explicit `HasDerivedCategory` instances in independent
  localization universes w and w'. Module carriers use `max u v`, allowing arbitrary
  module sizes at least as large as the coefficient ring.
- Derived reduction: `L` is equipped with the universal counit `ε` and the Mathlib
  `L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso ... (.up ℤ))` condition for
  termwise extension of scalars followed by localization. This specifies the same total
  left-derived scalar extension used in `SheafOfModules.derivedChangeOfRings`, interpreted
  on modules (the identity-covered one-object site). These are the data specifying the
  functor, not extra flatness, resolution, or marking hypotheses. The adjunction supplies
  additivity explicitly; no local instance or additional additive assumption is used.
- K pseudo-coherent: `(K : DerivedCategory ...) (hK : IsPseudoCoherent K)`, using the
  recorded definition without a copy.
- F a bounded-above complex of finite free quotient modules: `F : CochainComplex ... ℤ`,
  `b : ℤ`, `hFbound : F.IsStrictlyLE b`, and `hFterms` giving `Module.Free` and
  `Module.Finite` in every integer degree.
- The specified marking is the actual isomorphism `α : L.obj K ≅ Q.obj F`, not an
  existential isomorphism or a bare quasi-isomorphism claim.
- The output is a complex P, the actual isomorphism `β : Q.obj P ≅ K`, and an actual
  isomorphism of complexes `θ : (extendScalars ...).mapHomologicalComplex.obj P ≅ F`.
- P is finite free degreewise by the conjunction of `Module.Free` and `Module.Finite`.
  `P.IsStrictlyLE b` gives both boundedness and the last upper-bound clause of the node.
  Giving an arbitrary bound b of F up front is equivalent to its bounded-above hypothesis
  together with the assertion that every prescribed such bound can be retained.
- The final equality is `L.map β.hom ≫ α.hom = c_P ≫ Q.map θ.hom`. Here c_P is written
  explicitly as the canonical comparison: first `L.map (quotientCompQhIso ...).inv`,
  then the counit `ε`, then `Qh.map (mapHomotopyCategoryFactors ...).hom`, and finally
  `(quotientCompQhIso ...).hom`. Thus c_P has source `L.obj (Q.obj P)` and target
  `Q.obj (P ⊗ R/I)`. Because P is bounded above and free, c_P is the canonical
  isomorphism computing derived reduction. The equality is exactly the node's equation
  transported through this isomorphism, with the same orientation of α and β.

Dependency declarations read and used:

- `Sheaf.RingTheory.RingPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`: exactly a
  bounded-above finite-free representative isomorphic to K.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`, and `DerivedCategory.quotientCompQhIso`:
  localization and the canonical comparison between its complex and homotopy forms.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`, `SheafOfModules.derivedChangeOfRings`:
  the universal counit formulation and its computation on K-flat representatives. Its
  general sheaf statement is imported, not copied or replaced; the module-category
  formulation directly uses Mathlib's identical left-derived-functor universal property.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`, `ModuleCat.extendScalars` and
  `ModuleCat.extendRestrictScalarsAdj`: the actual quotient scalar extension.
- `Mathlib.Algebra.Homology.HomotopyCategory`, `Functor.mapHomotopyCategoryFactors`:
  the canonical passage from termwise extension of complexes to homotopy categories.
- `Mathlib.CategoryTheory.Functor.Derived.LeftDerived`, `Functor.IsLeftDerivedFunctor`:
  the universal property specifying derived scalar extension, with no substitute tensor.

All recorded proof-dependency modules are imported, including the Mathlib K-projective
map-representative and derived-homology-sequence modules. The declaration docstring contains
all seven proof steps, including the nilpotent Nakayama argument without finite-generation
assumptions, the split cokernel, finite freeness, preservation of b, and the signed cone
homotopy verifying the marking. The source was read in `more-algebra.tex` at
`lemma-lift-complex`, `lemma-lift-complex-projectives`,
`lemma-check-pseudo-coherent-modulo-nilpotent`, and `lemma-lift-complex-stably-frees`
(Tags 0BCA, 09AR, 0H76, 0BCB, respectively).

Edge cases checked: I=0 permits N=1 and reduces the marking problem to an isomorphism in
D(R); the zero ring is permitted (no Nontrivial assumption); zero F and rank-zero terms
are permitted; every integer upper bound b, including negative bounds, is retained;
complexes may be unbounded below. The termwise zero condition uses Mathlib's
`IsStrictlyLE`, meaning the module objects above b are zero objects, not merely that their
cohomology vanishes. No finite rank or characteristic restriction is introduced. The
one-plus-ideal condition is kept verbatim although nilpotence implies it mathematically.

Searches for existing statements (2026-10-15):

- `msearch.py` LeanFinder: “Lift a prescribed bounded above finite free complex model of
  derived reduction modulo a nilpotent ideal preserving its specified derived isomorphism”.
  Eight hits, all about formally smooth algebra liftings (`Algebra.FormallySmooth.exists_lift`,
  `exists_mkₐ_comp_eq_of_isAdicComplete`, `exists_kerProj_comp_eq_id`, and related maps).
  None concern the marked complex-lifting statement.
- `msearch.py` Loogle: `IsNilpotent, CochainComplex`: zero hits.
- `msearch.py` Mathlib grep: `nilpotent.*complex|complex.*nilpotent|marked.*lift`: zero hits.
- Source and project `rg` with that expression: project
  `PseudoCoherentNilpotentInvariance.lean` mentions projective complex lifting in its proof;
  other hits concern unrelated geometric marked points. No exact match.
- `grep -rn` for the node id in the upstream project: zero hits.
- Inspected project `StablyFreeComplexLift.lean`: its
  `DerivedCategory.exists_stablyFree_lift_mod_ideal` has no prescribed marking and no
  marking equality, so cannot be reused as this statement.
- Full declaration-name search in Mathlib, upstream sources, project sources, and
  `dag/lean_names_upstream.json`: no collision for
  `exists_marked_finiteFree_lift_of_nilpotent`.

Validation: the delivered file compiled cleanly with `scompile.py` on the server:
1.5 seconds, nice 19, two threads, 60-second per-file limit. No local compiler or global
build was run. The item JSON differs only in its `lean` field.

## Second reading by NC

I independently read the DAG node, the entire Lean module, all three statement-dependency
nodes and their recorded declarations, and More on Algebra at
`lemma-lift-complex` (0BCA), `lemma-lift-complex-projectives` (09AR),
`lemma-check-pseudo-coherent-modulo-nilpotent` (0H76), and
`lemma-lift-complex-stably-frees` (0BCB). The local statements introduce their rings and
ideals explicitly; no standing Noetherian, local, characteristic, or finiteness assumption
is missing. The marked refinement follows the node's explicit choice of delta and signed
cone homotopy, rather than being asserted as the verbatim conclusion of 0BCB.

Object, hypothesis, and conclusion checklist (all pass):

1. R is an arbitrary commutative ring; I is its ideal: `{R : Type u} [CommRing R]`
   and `(I : Ideal R)`. No field or nontriviality instance is added.
2. A positive nilpotence exponent: `hnil : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = 0`.
   This includes exponent one. The separate source/node unit assumption is retained
   literally by `hunits : ∀ x : I, IsUnit (1 + (x : R)))`.
3. K belongs to D(R): `K : DerivedCategory (ModuleCat.{max u v} R)`.
   The two `HasDerivedCategory` instances are precisely the localization size data of
   def-weil-abstract-derived-category. I opened Mathlib's `Q`, `Qh`, and
   `quotientCompQhIso`; they are localization of the actual complex and homotopy categories.
4. K is pseudo-coherent: `hK : IsPseudoCoherent K`. The imported
   `DerivedCategory.IsPseudoCoherent` is exactly an existential bounded-above complex of
   finite free modules with `Nonempty (Q.obj E ≅ K)`, as its dependency node requires.
5. Derived reduction is `L` with counit `ε` and `L.IsLeftDerivedFunctor ε ...`.
   I checked Mathlib's universal-property definition and the recorded
   `SheafOfModules.derivedChangeOfRings` signature. For modules, termwise change of rings
   is the existing `ModuleCat.extendScalars (Ideal.Quotient.mk I)`, with additivity
   supplied by its actual adjunction. The universal property specifies its total left
   derived functor, uniquely up to counit-compatible isomorphism. It does not postulate
   a new tensor operation or assume flatness of R/I. The sheaf theorem is imported for
   the proof's change-of-rings computation; no dependency replacement module is needed.
6. F is a complex over R/I: `F : CochainComplex (ModuleCat ... (R ⧸ I)) ℤ`.
   `hFbound : F.IsStrictlyLE b` supplies its bounded-above condition and `hFterms`
   supplies `Module.Free` and `Module.Finite` in every integer degree.
   Choosing an arbitrary bound b as input expresses both the bounded-above assumption
   and the node's final assertion about preserving any supplied upper bound.
7. The prescribed marking is the actual `α : L.obj K ≅ Q.obj F`, with the node's
   orientation, rather than mere existence of an unspecified isomorphism.
8. The existential witnesses are P over R, an actual `β : Q.obj P ≅ K`, and an actual
   complex isomorphism `θ : (extendScalars ...).mapHomologicalComplex.obj P ≅ F`.
   Thus theta identifies differentials as well as the individual quotient modules.
9. `P.IsStrictlyLE b` gives boundedness with the same bound. The following universal
   conjunction gives finite freeness of every P term. Neither conclusion requires the
   cohomology modules themselves to be free.
10. The last equality has source `L.obj (Q.obj P)` and target `Q.obj F`.
    On the left it is `L.map β.hom ≫ α.hom`. On the right the inverse of
    `quotientCompQhIso` first passes from Q(P) to Qh(P), epsilon computes derived
    reduction, `mapHomotopyCategoryFactors.hom` identifies termwise reduction in the
    homotopy category, and the target `quotientCompQhIso.hom` passes back to complexes
    localized by Q. The final arrow is `Q.map θ.hom`.
    I opened both natural isomorphism signatures to check these orientations. Hence
    this is exactly the node's marking equation under the canonical comparison; since
    P is bounded above and free this comparison is invertible. There is no extra
    marking hypothesis or conclusion, and the existential witnesses precede all their
    conditions as required.

Edge cases: zero ring, I=0, I=top when nilpotence permits it, zero K and F, and rank-zero
terms are admitted. Empty bases are not excluded by `Module.Free`/`Module.Finite`.
There is no index-set parameter, scheme, or characteristic restriction. N=0 is explicitly
excluded exactly as in the node; any nilpotent ideal admits a positive exponent. The bound
b can be any integer, including zero and negative integers, with no bound below. The
`IsStrictlyLE` predicate imposes zero objects termwise, not just cohomology vanishing.
Independent declared universes u,v,w,w' and module universe `max u v` accommodate arbitrary
module sizes above the coefficient universe; there is no independent test-object universe
that could make a hypothesis vacuous. Every variable and universe is explicitly bound.

Independent searches (2026-10-15), using different queries from the first reader:

- msearch LeanFinder: "A chosen derived isomorphism modulo a nilpotent ideal lifts to a
  finite free complex with compatible chain isomorphism". Eight hits, all formally smooth
  algebra/derivation liftings; none is a marked complex lift.
- msearch Loogle: `"lift", "CochainComplex"`. Twelve hits, consisting of cycle lifts and
  mapping-cone cochain/cocycle lifts; none has this statement.
- msearch Mathlib grep: `finiteFree.*lift|lift.*finiteFree`. Zero hits.
- Independent rg in Mathlib, upstream WeilConjectures, and project lean/Sheaf for
  `lift.*complex|complex.*lift|marked.*[Ll]ift`: resolution and cone-lifting tools occur,
  but no theorem giving the specified marking. I opened
  `DerivedCategory.exists_stablyFree_lift_mod_ideal` in StablyFreeComplexLift: its quotient
  representative hypothesis and existential complex isomorphism do not retain alpha or
  assert the compatibility equation, so it is not an existing match.

H4-H9 audit: no definitions, hollow data, auxiliary proved facts, local notation or private
copies were introduced. The sole theorem has only `sorry` as proof. Its docstring names
all seven proof steps of the DAG node, including nilpotent Nakayama without finite
hypotheses, degreewise splitting, finite freeness, bound preservation and the signed
homotopy. Source and blueprint tags are present. The imports include the statement and
recorded proof-dependency interfaces. There are no new definition nodes, dependency
modules or statement corrections to audit under H12/H13 or 4c.

Mismatches found: none. I preserved the Lean source and node record verbatim and added
this independent review. The node's `lean.statement` equals the entire signature in the
module verbatim. Fresh server validation through scompile.py passed cleanly in 1.4 seconds
(nice 19, two threads, 60-second per-file limit); no local compiler or global build was run.
