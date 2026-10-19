## Worker report

The module `Sheaf.Paper.StratifiedLattice` states
`AlgebraicGeometry.ProEtale.CondensedRing.exists_stratified_lisse_integral_lattice`.
The single theorem has proof `sorry`. There are no new definitions, auxiliary theorems,
new nodes, dependency repairs, or changes to the natural-language statement. The delivered
node differs from its base only in `lean`. Its signature is extracted verbatim from the
file, preserving its line breaks. Source: main-20261015 blueprint,
`sec-six-functors-basics/sk-lem-stratified-lattice/_section.md` and the seven recorded
proof steps. The declaration docstring gives all seven steps and their dependency ids.

Hypothesis and clause correspondence:

- The fixed prime ell is `(l : ℕ) [Fact l.Prime]`. The finite extension is
  `(E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The local instance `spectralNorm.nontriviallyNormedField ℚ_[l] E` installs exactly
  the canonical extending topology; no arbitrary topology or norm is a hypothesis.
  Coefficients use the upstream Type-zero topological-ring interface on an arbitrary
  scheme universe `u`; the site object universe remains `u+1`, its morphism universe
  remains `u`, and abelian sheaf values remain `u+1`. No equality of site universes is
  imposed. Finite extensions are small fields (they have a finite basis over ℚ_l).
- The valuation ring is exactly `Padic.coefficientExtensionIntegers l E` from the
  recorded coefficient-extension dependency, with its subspace topology. Its uniformizer
  is already chosen in that dependency. Neither the conclusion nor its construction
  depends on this choice, so no new uniformizer or uniformizer hypothesis is introduced.
  The preliminary discussion of finite coefficient quotients motivates using integral
  lattices; the theorem does not assert that every rational lisse module has a global
  integral model or directly comes from a finite quotient.
- The standing field and positive characteristic are `(p : ℕ) [Fact p.Prime]`
  and `(k : Type u) [Field k] [CharP k p]`. For a field, specifying a prime positive
  characteristic is equivalent to positive characteristic. `_hpl : p ≠ l` is precisely
  the required inequality.
- `X : Scheme.{u}` together with `[X.Over (Spec (.of k))]` gives a scheme over the
  fixed field. `[IsSeparated (X ↘ Spec (.of k))]` is separatedness. The two instances
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]` jointly express finite type, as in the project's
  recorded finite-type convention. No separate Noetherian, qcqs, dimension, normality,
  reducedness or connectedness hypothesis is added.
- `B := Profinite.continuousMapRingObj.{u} E` is the condensed topological field, and
  `A := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)`
  is its condensed valuation ring. `condensedRingObj B X` and `condensedRingObj A X`
  are the underlying ring objects of the recorded `coefficientRing X` construction.
  Thus these are the actual pulled condensed coefficients, without substituting
  continuous-function sheaves for them or assuming an unrecorded comparison.
- `L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)`
  quantifies over the stipulated internal module objects in abelian sheaves on the
  small pro-etale site. `LocallyFree (condensedRingObj B X) L` is exactly the existing
  pro-etale-cover predicate: on each member `Mod.IsFree` gives an isomorphism to a
  finite direct sum of the regular coefficient module. The rank can vary with the
  covering member and zero is allowed.
- `∃ S : Scheme.FiniteLocallyClosedStratification X` uses the recorded exact finite
  stratification interface. Its fields give `Fin S.n`, locally closed underlying
  strata, pairwise disjointness, covering, schemes `S.domain i`, immersions, and equality
  of their images with the designated strata. No constructibility hypothesis beyond
  the node's finite locally closed notion is added. `∀ i : Fin S.n` covers every stratum.
- The displayed `LT` is `(CondensedRing.upperStar B (S.immersion i)).obj L`: the canonical
  restriction to that stratum, with the coefficient comparison already included by the
  existing ringed pullback functor. It has coefficients `condensedRingObj B T` for
  `T := S.domain i`.
- The quantified `M` is an internal module over `condensedRingObj A T`, and
  `LocallyFree (condensedRingObj A T) M` says precisely that this integral module is
  lisse, with varying finite ranks allowed.
- The map `a : A ⟶ B` is the existing continuous-ring-sheaf-map construction applied
  to the actual valuation-subring inclusion, followed by the existing forgetful
  sheaf-compose functor. Its pullback `aT := (upperStarFromPoint T).map a` is the
  required integral-to-rational coefficient map. Both are concrete terms in the
  signature, with no extra existential map or arbitrary choice.
- `ι : M ⟶ (Mod.comap aT).obj LT` is an integral-linear map to the given rational
  module restricted to integral coefficients, and `Mono ι` says it embeds a submodule.
  The final `IsIso (((Mod.extendRestrictAdjunction aT).homEquiv M LT).symm ι)` says
  that the canonical scalar extension of this very inclusion is an isomorphism.
  Under the existing extension/restriction adjunction this is exactly
  `E_T ⊗_{O_E,T} M → LT`, not an unrelated existential isomorphism. The node's
  proof step 1 identifies this coefficient extension with inversion of ell, so it
  gives `M[1/l] = L|_T` in the invariant sense of the stated canonical isomorphism.
- The nodal example and warning about the failure of global lattices are motivation
  in the source preceding its final lemma paragraph. The delivered conclusion is the
  final lemma, not a claim of a global lattice or a formal construction of that example.

Dependency declarations read and used:

1. `def-weil-l-adic-coefficient-extension` records
   `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
   `Padic.finite_coefficientExtensionRing`. Its public import
   `Sheaf.NumberTheory.Padics.CoefficientExtension` supplies the actual
   `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionAbsoluteValue`
   and `Padic.coefficientExtensionUniformizer`; their signatures and docstrings were
   read. The actual integer subring is used, not another definition of the valuation ring.
2. `sk-def-sfb-pulled-back-coefficients` records
   `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
   `AlgebraicGeometry.ProEtale.coefficientRing` and
   `AlgebraicGeometry.ProEtale.condensedRingObj`. Both signatures and their bodies
   were read in the stipulated framework overlay. The latter is exactly the underlying
   object of the former; its inherited monoid structure is the strong monoidal pullback.
3. `sk-def-sfb-module-objects` has no `lean` record, but its closed slopmaster2 audit
   explicitly binds the Mathlib declarations in `Mathlib.CategoryTheory.Monoidal.Mod`:
   `CategoryTheory.ModObj`, `CategoryTheory.Mod`, `CategoryTheory.Mod.forget` and
   `CategoryTheory.Mod.regular`. Their full signatures, action laws and docstrings were
   read. The theorem uses this category through the published module-object framework.
4. `def-constructible-stratification` records
   `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
   `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`. The full structure
   and its parent topological structure were read, including all covering and image fields.
5. The existing `CategoryTheory.Mod.IsFree` in
   `WeilConjectures.CategoryTheory.ModuleObjects.Free` means an isomorphism to
   `Mod.finiteFree R n`, the biproduct of `Fin n` copies of `Mod.regular R`.
   The published proof dependency `Sheaf.Paper.ContinuousLocallyFreePullback` exports
   `AlgebraicGeometry.ProEtale.CondensedRing.LocallyFree`, the exact pro-etale-cover
   predicate required here. It is publicly imported because it occurs in the signature.
   The module was read via `scompile.py --source`, since the shared older snapshot
   does not contain it.
6. Restriction is the real
   `AlgebraicGeometry.ProEtale.CondensedRing.upperStar` from
   `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.
   Scalar extension and its adjunction are `CategoryTheory.Mod.extendScalars`,
   `CategoryTheory.Mod.comap` and `CategoryTheory.Mod.extendRestrictAdjunction`
   from `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`; their signatures,
   unit and extension formulas were read. These come through the existing imports.

The available recorded proof modules are imported: continuous coefficient realizations,
continuous etale-local lattices, etale stratified finiteness, continuous local-freeness
pullback, finite-etale splitting, lattice-sheaf local constancy, and extension integers DVR
(the latter through the coefficient module). The Mathlib Noetherian and PID modules give
exact matches for the other recorded proof leaves. `det-prop-sfb-qlbar-colimit-x-invert-ell`
has no declaration/module to import; it remains named in the proof docstring. It is a
proof dependency, not a missing object needed to type this statement. No import cycle is
introduced by the new module.

Edge cases checked before writing and again against the signature: the empty scheme can
use `S.n = 0`; no positive-stratum or nonempty-cover binder excludes it. `Mod.IsFree`
allows `n = 0`, and the zero lattice has monic inclusion and isomorphic rationalization.
No common global rank is imposed. Disconnected and nonreduced schemes, arbitrary finite
ramification of E, and the nodal nonnormal example are included. The conclusion allows
several strata and never requires a lattice on all of X. The characteristic condition is
stated exactly; no algebraic closure or finite-base-field assumption is present.

Searches performed before writing:

- `msearch.py ... leanfinder`: "A lisse sheaf over a finite extension of the l-adic
  numbers has a locally free integral lattice after a finite stratification".
  Eight hits: `Profinite.NobelingProof.Nobeling_aux`, `LocallyConstant.freeOfProfinite`,
  `ZLattice.module_free`, `Condensed.finFree`,
  `Module.isLocallyConstant_rankAtStalk_freeLocus`, `ZLattice.module_finite`,
  `IsIntegralClosure.module_free`, `Module.isLocallyConstant_rankAtStalk`.
  These concern unrelated algebraic/discrete lattices or finite free objects, not
  integral structures on finite strata for the pulled condensed coefficients.
- `msearch.py ... loogle`: `AlgebraicGeometry.Scheme, "lattice"`.
  Three hits, the complete lattice, complete semilattice supremum and semilattice
  infimum instances on `Scheme.IdealSheafData`; none is the claimed theorem.
- `msearch.py ... leansearch`: "A lisse sheaf over l-adic coefficients admits integral
  lattices on a finite locally closed stratification". Eight hits on `ZLattice`,
  `LocallyRingedSpace.𝒪`, locally constant condensed sets, and adhesivity of sheaves;
  no matching theorem.
- `msearch.py ... grep`: `stratif.{0,30}lattice|lattice.{0,30}stratif`: zero Mathlib hits.
- `rg` of the source `WeilConjectures` and project `lean/Sheaf` for the item id,
  stratified lattices and integral/lisse interfaces found the lattice-pair/classification,
  etale-local lattice and constructible-integral-lattice modules. They use sectionwise
  continuous modules or assert different global constructibility conclusions, so none
  states this internal module theorem. Searches of `dag/lean_names_upstream.json`
  found no matching declaration name. The broader internal-module search located
  `Mod.IsFree` and, after checking the recorded proof node, the exact existing
  `CondensedRing.LocallyFree`, which is reused.
- Read `lem-sfb-topological-stratified-lisse-lattices`: it has no Lean record and a
  different general topologically Noetherian statement (and requires constructible
  strata). It is not an existing declaration of this standing-scheme lemma.

No statement is disputed and no node fault requiring correction was found.

Validation: `scompile.py Q60 sk-lem-stratified-lattice` compiled the delivered file
cleanly, both under the temporary sandbox module and its actual library module name
(the actual module pass took 26.9 seconds). There were no errors or warnings. Only the
single requested theorem is postponed. No global build, direct Git operation, or write
to the read-only project/source trees was performed.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
