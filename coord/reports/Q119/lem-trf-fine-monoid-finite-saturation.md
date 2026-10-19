## Worker report

`Sheaf.GroupTheory.FineMonoidFiniteSaturation` states `fine_monoid_finite_saturation`, with
one postponed theorem and no definitions. The node and all its natural-language fields are
unchanged; only `lean` is added. There are no new nodes, dependency repairs or statement corrections.

Clause-by-clause comparison:

* The additive commutative monoid is `(P : Type u) [AddCommMonoid P]`.
  `[AddMonoid.FG P]` is finite generation. `hP : Function.Injective
  (GrothendieckAddGroup.of (M := P))` is exactly integrality, as the node defines it.
* `GrothendieckAddGroup P` is the canonical `G = P^gp`. The existential additive submonoid
  `Q` is identified by `∀ g, g ∈ Q ↔ ∃ n : ℕ, 0 < n ∧ n • g ∈ Set.range
  (GrothendieckAddGroup.of (M := P))`. This is exactly the node's root saturation; its
  carrier and operations are determined by this identification. This introduces the
  object defined in the item itself, rather than assuming another choice of saturation.
* `AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative Q)` uses the existing project's
  definition of finitely generated, integral and saturated. `Multiplicative` only changes
  notation; it imposes no torsion-freeness condition. Its definition uses the canonical
  group completion. The canonical additive equivalence `e` in the next clause, normalized
  by `e (GrothendieckAddGroup.of q) = q.1`, identifies that completion with the original `G`.
* `∃ F : Finset (GrothendieckAddGroup P), (∀ f ∈ F, f ∈ Q) ∧ ...` gives the finite subset
  and the equality `Q = ⋃ f ∈ F, {x | ∃ p : P, x = f + GrothendieckAddGroup.of p}`.
  Thus the translates are precisely `f + P`, inside the original group.
* `∀ S : AddSubmonoid P` includes every submonoid without a finite-generation assumption.
  The left root set consists of `x` with `n • x = of p - of s`, `n > 0`, `p : P`, `s : S`.
  The right consists of `q-s`, `q : Q`, `s : S`. Both sides are subsets of the original
  `GrothendieckAddGroup P`, including when `P-S` has nontrivial units or torsion.
* The last clause supplies `i : P →+ Q` normalized by `(i p).1 = GrothendieckAddGroup.of p`.
  This equation determines its value at every input, hence gives the canonical inclusion,
  rather than an arbitrary map or extra assumption. It quantifies every commutative ring
  `(R : Type v) [CommRing R]`. The induced map is
  `AddMonoidAlgebra.mapDomainRingHom R i`. Mathlib's `RingHom.Finite` (read in
  `Mathlib/RingTheory/Finiteness/Defs.lean:170`) means `Module.Finite R[P] R[Q]` for the
  module structure induced by that exact ring map. Thus it states precisely finite
  generation of the monoid algebra over the original monoid algebra, using Mathlib's
  existing definition rather than a private finite-spanning predicate.

Dependency declarations read and used:

* Statement dependency `def-trf-fs-log-blowup`: imported recorded module
  `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`. Its primary declaration
  `AlgebraicGeometry.IsSaturatedLogBlowup` and docstring were read. The needed monoid
  predicate is `AlgebraicGeometry.IsFineSaturatedMonoid`, supplied through that module
  from `Sheaf.AlgebraicGeometry.LogRegularPair`, whose full definition and docstring were
  read. It is exactly the fine/saturated monoid notion stated in the dependency.
* Mathlib supplies `Algebra.GrothendieckAddGroup` and `Algebra.GrothendieckAddGroup.of`
  (`Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup`), `AddMonoid.FG`
  (`Mathlib.GroupTheory.Finiteness`), `AddMonoidAlgebra.mapDomainRingHom`
  (`Mathlib.Algebra.MonoidAlgebra.MapDomain`), and `RingHom.Finite`
  (`Mathlib.RingTheory.Finiteness.Defs`). Their definitions/signatures and docstrings
  were inspected. No second definition of any of these notions is introduced.
* Proof dependency `lem-trf-fg-torsionfree-group-free` has status `mathlib` and match
  `Module.basisOfFiniteTypeTorsionFree'` in `Mathlib.LinearAlgebra.FreeModule.PID`.
  Its full signature/docstring were read, and its module is a plain proof import.
* Proof dependency `lem-trf-gordan-rational-cone-finite` records
  `gordan_rational_cone_finite` in `Sheaf.Paper.GordanRationalCone`; the module's full
  theorem and proof docstring were read and its module is a plain proof import.

The source was opened with `pdftotext -layout` on the project's ILO PDF. Printed p. 101,
VIII 3.1.17 defines saturation by positive powers in the group completion and states
localization compatibility. Printed p. 104, VIII 3.2.9 proof states the finite saturation
morphism. Only its finiteness assertion is used, as the node explicitly requires; its
normalization assertion is not part of this theorem. The docstring transcribes all four
node proof steps, including the finite torsion reduction and its two named proof dependencies.

Edge cases checked: `P=0` (trivial completion and singleton translate representative),
`P=ℕ`, `P=2ℕ` regarded in its own completion `2ℤ` (not an incorrectly enlarged ambient `ℤ`),
`P=⟨2,3⟩` (saturation `ℕ`, translates by `0,1`), `P=ℕ²`, and the monoid generated by
`(1,0),(1,1)` inside `ℤ ⊕ ℤ/2` (torsion requires two translates). For `S=⊥` localization
reduces to the original saturation; for `S=P` both localized sides are `G`. Zero and arbitrary
commutative coefficient rings and independent universes `u,v` are admitted. The multiplier
is a natural number with `0<n`, so it excludes only the forbidden zero multiplier. There
is no torsion-free hypothesis and no requirement that `S` be finitely generated.

Searches actually run via `/home/ubuntu/weil-launcher-nt/msearch.py Q119
lem-trf-fine-monoid-finite-saturation`:

* `leanfinder`: “For a finitely generated integral commutative monoid, its root saturation
  in the group completion is finite over it and commutes with localization”. Eight hits,
  including `Localization.fg`, `AddLocalization.fg`, `GrothendieckGroup.instFG`,
  `GrothendieckAddGroup.instFG` and `IsAffineMonoid.toFG`. None gives root saturation,
  finite translates or saturation/localization compatibility.
* `loogle`: `AddSubmonoid.saturation, Submonoid.PowSaturated,
  Algebra.GrothendieckAddGroup, Module.Finite`. Zero hits.
* `leansearch`: “The root saturation of a finitely generated integral monoid in its group
  completion is finitely generated and finite as a module, and saturation commutes with
  localization”. Eight hits: `Subalgebra.saturation`, finite localized-module results,
  `Localization.fg`, and the Grothendieck-group instances. These concern different
  saturation or localization finiteness statements, not this theorem.
* `grep`: `PowSaturated|AddSaturated|rootSaturation|saturation`, subdirectory `GroupTheory`.
  Five hits in `GroupTheory/Subgroup/Saturated.lean`, defining `Submonoid.PowSaturated`.
  Read that file: it defines root-closedness, with additive version
  `AddSubmonoid.NSMulSaturated`, but supplies no root-saturation construction or finiteness
  theorem. Direct Mathlib `rg` also found divisor-closed `Submonoid.saturation` in
  `Algebra/Group/Submonoid/Saturation.lean`, which has a different meaning.
* Direct `rg` over the full upstream `WeilConjectures` tree for
  `root[Ss]aturation|root_saturation|fine_monoid_finite_saturation|[Mm]onoid.*saturation|saturation.*[Mm]onoid|IsFineSaturated`
  and the item ID found no relevant declaration. Direct `rg` of Mathlib and the upstream
  name index for `fine_monoid_finite_saturation|fine.*monoid.*saturat|monoid.*finite.*saturat`
  found no theorem. Direct `rg` over `lean/Sheaf` found the existing
  `IsFineSaturatedMonoid` definition and its uses, which this statement reuses.

The existing `Sheaf.Paper.GordanRationalCone` dependency is a legacy (non-`module`) file.
Lean rejects importing it into a file with the new `module` header, so this statement file
uses the compatible legacy layout and retains both required proof imports. This changes
no mathematical declaration or dependency record.

No `STATEMENT-DISPUTED` or mathematical node fault remains.

## Second reading by Q119

I reopened the node and the revised module for a separate clause-by-clause reading (the
maintainer performs the independent review). I removed the initial `let` abbreviations to
meet the project statement convention and replaced the handwritten finite-spanning condition
by the exact existing Mathlib `RingHom.Finite` predicate on the canonical induced map.
The final signature matches `P` with `[AddCommMonoid P]`, finite generation with
`[AddMonoid.FG P]`, and integrality with injectivity of the canonical completion map.
The root-submonoid equivalence uses positive natural multiples in that exact completion.
`IsFineSaturatedMonoid` gives all three requested properties, and `e` identifies the
completion while fixing the monoid elements. The finite translates have `F⊆Q` and use
`of p`; no ambient larger group is substituted. The localization clause includes every
`S`, and its two subsets use the same original group, including torsion cases. The final
inclusion is fixed element-by-element and its ring map is finite for every commutative
coefficient ring. No new definition or additional hypothesis is present. Every theorem proof
is `sorry`; no inline proof obligations or file-local notation occur in the signature.

Validation: prescribed `scompile.py` completed with exit code 0 for both the sandbox
copy and `Sheaf/GroupTheory/FineMonoidFiniteSaturation.lean`, without warnings.
