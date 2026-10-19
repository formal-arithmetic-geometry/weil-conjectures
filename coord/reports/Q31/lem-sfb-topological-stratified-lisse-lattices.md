## Worker report

The module `Sheaf.Paper.TopologicalStratifiedLisseLattices` states
`AlgebraicGeometry.ProEtale.exists_topological_stratified_lisse_lattices`, with its
whole proof `sorry`. It defines no new objects and leaves the natural-language
statement and every other existing node field unchanged except `lean`.

Hypothesis and conclusion correspondence:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The specified finite subextension of the fixed p-adic algebraic closure:
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. This is the finite-dimensional
  intermediate field, with its fixed embedding and induced coefficient topology.
- Scheme and topological Noetherianity: `(X : Scheme.{u})`
  `[TopologicalSpace.NoetherianSpace X]`. No scheme-theoretic Noetherianity,
  normality, reducedness, or invertibility of ell is imposed.
- The rings on every T: `condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) T`
  and `condensedRingObj (Profinite.continuousMapRingObj E.1) T` are exactly the
  pulled condensed O_E and E. The inclusion is the dependency's
  `padicIntegersToPadicSubfield T ℓ E`, not a newly selected map.
- Internal rational module: the binder `L : Mod (Sheaf (Scheme.ProEt.topology X)
  Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj E.1) X)`.
- Lisse: `hL : CondensedRing.LocallyFree ... L`. The existing abbreviation says
  that a `Scheme.Cover.{u} Scheme.proetalePrecoverage X` makes the module
  `Mod.IsFree` on each member; `Mod.IsFree` existentially chooses a natural rank
  separately on each member and identifies it with a finite biproduct of regular
  modules. Thus ranks are finite and need not be constant.
- Finite locally closed subschemes partitioning X:
  `∃ S : Scheme.FiniteLocallyClosedStratification X`. The recorded dependency
  supplies `S.n`, pairwise disjoint locally closed sets covering X, schemes
  `S.domain a`, immersions `S.immersion a`, and the prescribed set-theoretic images.
- Constructibility: the explicit additional clause
  `∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)`.
- Integral lisse module on every stratum: `∀ a : Fin S.n, ∃ L₀ : Mod ...,
  CondensedRing.LocallyFree ... L₀ ∧ ...`, over the coefficient on `S.domain a`.
- Restriction of L to that stratum: the canonical
  `(CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
  (S.immersion a)).obj L`; it uses the published ringed-topos pullback and the
  canonical coefficient comparison, without replacing it by an arbitrary functor.
- Submodule: `∃ ι : L₀ ⟶ (Mod.comap ...).obj (L|S_a), Mono ι ∧ ...`.
  An integral subobject is precisely an integral module with a monic inclusion
  into the restricted rational module. Its categorical image gives the literal
  submodule formulation, with the same integral module up to its canonical image
  isomorphism. No rational-linearity is demanded of this integral inclusion.
- The inclusion induces the required isomorphism: `IsIso (Mod.extendHom
  (padicIntegersToPadicSubfield (S.domain a) ℓ E) ι)`. The read source of
  `Mod.extendHom` shows that this is the adjoint map B tensor_A L₀ -> L|S_a,
  whose underlying bilinear formula is b tensor n -> b times ι(n).
  Mere existence of some isomorphism would miss this compatibility; the
  statement requires this particular map to be invertible.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `coefficientRing_X`, `condensedRingObj`,
  `isCommMonObj_condensedRingObj` in `AlgebraicGeometry.ProEtale`. The bundled
  and unbundled presentations share the same actual inverse-image construction.
- `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`:
  `AlgebraicGeometry.ProEtale.padicIntegersToPadicSubfield` and its condensed
  point inclusion. Read through `scompile.py --source`, since the old local
  checkout lacks the current source. These are the exact published dependency
  declarations and are not restated.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.ModObj`, `Mod`,
  `Mod.regular`, `Mod.forget`, and `Mod.comap`. The module-object dependency has
  no lean record but has a closed slopmaster2 audit naming these Mathlib
  declarations; its source signatures, action laws, and regular module were read.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`, the dependency's
  newly repaired interface without an extra constructibility condition.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension` import: the recorded general finite-extension
  coefficient constructions and positive-level finiteness theorem were read.
  The present coefficients use their specified embedded finite-subfield
  specialization from the integral-inclusion dependency.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Existing auxiliary APIs: `CondensedRing.LocallyFree` in
  `Sheaf.Paper.ContinuousLocallyFreePullback`; `CondensedRing.upperStar` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`;
  `Mod.extendHom` in `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`.
  All are reused directly; the latter two arrive through the public framework.

All recorded proof-dependency modules are imported, either explicitly as proof
imports or through the public framework imports already needed by the signature.
For the three proof dependencies without lean records, the audited declarations
are `isIso_condensedPullbackHom` in `ModuleObject.Basic`, and
`CondensedRing.upperStar`/`upperStarComp` in `ModuleObject.UpperLowerStar.Defs`.
The theorem docstring carries all six proof steps and their node references.

Source checks: read the first paragraph of Bhatt--Scholze Lemma 6.8.13 directly
from the local PDF (pdftotext), and the current main-20261015 blueprint proof of
`thm-sfb-extend-scalars-localization`, essential-surjectivity paragraph. The PDF
explicitly first proves the existence of lattices after a finite stratification;
the present statement does not assert a global lisse integral lattice.

Edge cases checked before drafting: X empty permits S.n = 0 and vacuous stratum
requirements. The zero module permits rank 0 in `Mod.IsFree` and its integral
zero model; the induced zero-object map is invertible. Ranks can vary by cover
member and by stratum. Disconnected and nonnormal schemes are included. A
one-point scheme permits the single stratum. No nonempty stratum condition or
fixed positive rank was introduced. The scheme universe u is unrestricted and
abelian sheaves have the framework's required universe u+1.

Searches made on 2026-10-18, all through the prescribed Q31 msearch wrapper:

- leanfinder: `A lisse p-adic sheaf on a topologically Noetherian scheme has
  integral lisse lattices on a finite constructible locally closed stratification`.
  Eight hits: Noetherian schemes, condensed discrete modules, and finite-type
  module sheaves; no matching theorem.
- loogle: `"Sheaf", "lattice"`. Five complete-lattice instances for submodules
  and ideal sheaves; no stratified integral-lattice existence theorem.
- grep: `[Ll]isse|[Ss]tratif.*[Ll]attice|[Ll]attice.*[Ss]tratif`. Three unrelated
  Mathlib separatedness hits; no match.
- leansearch: `A lisse p-adic sheaf has integral lisse lattices on finitely many
  constructible strata`. Eight hits concerning PadicInt, discrete condensed
  objects, and Z-lattices; no matching theorem.
- rg over the permitted upstream WeilConjectures tree and side lean/Sheaf:
  `lem-sfb-topological-stratified-lisse-lattices|stratified.*lattice|stratified.*Lattice`:
  no exact declaration. Broader lattice searches found the sectionwise global
  constructible-lattice statement and the continuous local/descent statements,
  which have different conclusions and were reused where appropriate.
- rg for `exists_topological_stratified_lisse_lattices` in
  dag/lean_names_upstream.json, upstream WeilConjectures, and lean/Sheaf:
  no preexisting declaration with the proposed name.

Validation: scompile.py compiled the sandbox and final module individually with
no errors or warnings (2.7 seconds and 3.3 seconds on the successful pass).
The initial pass exposed missing standard scoped object instances; opening
`CategoryTheory.Obj` and `CategoryTheory.Functor` repaired that without changing
the mathematical signature. No new nodes, dependency repairs, statement
corrections, or disputed statements were needed.

## Second reading by Q31

Solo reread of the node and completed Lean file, under the dispatcher's explicit
instruction not to start other agents; independent maintainer review remains
part of the delivery process. This is not a claim of a second worker's review.
Checked the prime and embedded finite-extension binders, topological rather than
scheme Noetherianity, and both pulled coefficient objects against the node.
Checked that `LocallyFree` quantifies a cover before choosing ranks, that S has
finite disjoint locally closed images covering X, and that constructibility is
explicit. Checked that each L₀ is integral and lisse, that its monomorphism has
the restriction-of-scalars target, and that `IsIso` concerns the scalar extension
of that very monomorphism. No mismatch was found and no node text changed.
