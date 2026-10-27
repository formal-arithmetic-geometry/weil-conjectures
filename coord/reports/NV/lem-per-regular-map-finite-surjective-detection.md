## Worker report

The module `Sheaf.RingTheory.RegularMapFiniteSurjectiveDetection` states
`RingHom.isRegular_of_finite_surjective_baseChange`. Its sole theorem has proof `by sorry`;
there are no new definitions, helper theorems, dependency repairs, or statement corrections.
The node is unchanged except for `lean`.

The source is Greco, *Two theorems on excellent rings*, Proposition 1.2, converse,
printed p. 140, with P geometrically regular as in Definition 1.1. I read the publisher
scan through https://scispace.com/pdf/two-theorems-on-excellent-rings-2lc74dyy3w.pdf,
pages 139–140. The foreword assumes commutative Noetherian rings throughout; Proposition
1.2 assumes flatness and a finite algebra surjective on spectra and detects the fibre
property after its canonical tensor base change. This confirms the node without correction.

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| R, Λ, R' are commutative rings | `{R : Type u} {Λ : Type v} {R' : Type w}` and the three `CommRing` instances |
| All three rings are Noetherian | `[IsNoetherianRing R] [IsNoetherianRing Λ] [IsNoetherianRing R']` |
| u : R → Λ | `[Algebra R Λ]`, with u the explicit `algebraMap R Λ` |
| u is flat | `hflat : (algebraMap R Λ).Flat` |
| v : R → R' | `[Algebra R R']`, with v the explicit `algebraMap R R'` |
| R' is finitely generated as an R-module via v | `[Module.Finite R R']` for precisely that algebra's module structure |
| Every prime p of R is the contraction of a prime of R' | `hsurj : ∀ (p : Ideal R) [p.IsPrime], ∃ p' : Ideal R', p'.IsPrime ∧ Ideal.comap (algebraMap R R') p' = p` |
| Tensor-product algebra Λ ⊗_R R' | Mathlib's `TensorProduct R Λ R'`, with its standard commutative-ring structure |
| u' sends r' to 1 ⊗ r' | `(Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R Λ R').toRingHom` |
| u' is regular | `hregular : RingHom.IsRegular` of that exact canonical inclusion |
| u is regular | `RingHom.IsRegular (algebraMap R Λ)` |

An algebra structure is the data of a unital ring map between these commutative rings.
Thus parameterizing u and v by the two algebra structures covers all maps of the node,
without a compatibility assumption beyond being maps out of R. In particular no flatness
or injectivity is assumed for v. `Ideal.comap` is literally ideal preimage. The explicit
canonical `includeRight` is used because the tensor ring's default algebra structure is
from its left factor; no second tensor product or private construction is introduced.
The regularity predicate itself installs the module structure of its supplied ring map.

Statement dependencies, with their full source signatures and docstrings read:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; it means every ideal is finitely generated.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat`, `Mathlib.RingTheory.RingHom.Flat`;
  flatness of the module for the supplied map. The source's `flat_algebraMap_iff`
  identifies it with `Module.Flat` for the algebra structure.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`; its field is finite generation of the top submodule.
- `def-weil-pbc-module-tensor-product`: the recorded Mathlib match `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with the quotient construction, `mk`,
  `lift`, and `ext'` read. The algebra structure and canonical `includeRight` are in
  `Mathlib.RingTheory.TensorProduct.Basic`, which is publicly imported.
- `def-weil-pbc-g-ring`: `RingHom.IsRegular`,
  `WeilConjectures.RingTheory.GRing`, including its use of
  `Algebra.IsGeometricallyRegular` and `Ideal.Fiber`. This is flatness plus geometrically
  regular Noetherian fibres, not regular sequences or just regular total rings.

Plain proof imports retain the node's complete proof plan:

- `Mathlib.RingTheory.Localization.AtPrime.Basic`: recorded `Localization.AtPrime`;
  `Ideal.ResidueField` and `Ideal.Fiber` are available from the regular-map module.
- `Mathlib.RingTheory.TensorProduct.Maps`: `Algebra.TensorProduct.cancelBaseChange`.
- `WeilConjectures.FieldTheory.CommonExtensionFields`: `Field.exists_common_extension`.
- `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`:
  `IntermediateField.adjoin_rank_le_of_isAlgebraic_right`.
- `WeilConjectures.RingTheory.GeometricallyRegularFieldExtension`:
  `Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and
  `Mathlib.LinearAlgebra.Basis.VectorSpace`: the recorded faithful-flat tensor-product
  instance and `Module.Free.of_divisionRing` supply faithful flatness after a field extension.
- `WeilConjectures.RingTheory.RegularRingFaithfullyFlatDescent`:
  `IsRegularRing.of_faithfullyFlat`.

The theorem's docstring gives every one of the node's six proof steps, including the
canonical residue-field map, pure-tensor cancellation formulas, common field and compositum,
finite field-extension regularity, faithful-flat descent, and assembly of the fibres.

Edge cases checked before writing:

- Zero rings are admitted: no `Nontrivial` assumption is added. If R is zero, its spectrum
  is empty and the regularity conclusion is flatness plus an empty fibre condition.
  If R' is zero, surjectivity on spectra forces R to have empty spectrum as well.
- Λ may be zero. Its fibres are zero rings, and the regular-ring convention admits them.
- Identity base change R' = R is allowed and recovers the given regularity under tensor
  cancellation. No nontrivial extension or positive degree is required.
- The finite map v need not be flat: for example Z → Z × (Z/2Z) has surjective spectrum
  and finite target module while its target module is not flat. The statement includes it.
- Neither characteristic nor finite type of u is restricted. Finite generation is as a
  module for v, not finite cardinality or finite generation of u as an algebra.
- The universes u, v, w are explicitly independent. There is no small test-field universe
  in this theorem and no additional equality of ring universes. The existing geometric
  regularity definition uses its recorded maximum universe; finite extensions can be
  transported there as in the existing field-extension theorem.
- Surjectivity is not hollow: a nonzero R mapping to the zero ring fails it. Flatness is
  not hollow either (e.g. Z → Z/2Z fails it).

Searches (all on 2026-10-24):

- `msearch.py leanfinder`, query “A flat ring map is regular if its base change by a finite
  algebra surjective on prime spectra is regular”: eight hits, consisting of flat and
  faithfully flat base-change results for regular sequences and flat ring maps. No match.
- `msearch.py loogle`, query `RingHom.IsRegular`: zero hits; identifier absent from Mathlib.
- `msearch.py grep`, query `IsRegular.*surject|geometrically.?regular|IsGRing`, subdirectory
  `RingTheory`: zero hits.
- `msearch.py leansearch`, query “Regular ring homomorphisms descend after finite surjective
  base change”: eight hits, on generic property descent, regular sequences, étale and
  finite base change, and surjective flat morphisms. None states this theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `finite_surjective|finiteSurjective|IsRegular.*(base|surj)|regular.*finite.*surj` and the
  node id: no matching regular-map detection theorem; hits concern unrelated scheme
  descent, regular immersions, and an existing regular-composition fibre calculation.
- Broader `IsRegular` and declaration-header inspection in `RingTheory/Regular*.lean`
  finds ascent, base change, permanence under composition, and faithfully flat descent
  of regular rings, with different statements. The chosen declaration name is absent
  from Mathlib, the upstream-name index, WeilConjectures, and Sheaf.

Validation: `scompile.py NV lem-per-regular-map-finite-surjective-detection` compiled the
module in both sandbox and library contexts, in 1.3 s and 1.2 s respectively, with no errors
or warnings. All universes and variables are explicit and `autoImplicit` is disabled.
The only postponed proof is the named theorem matching this DAG node.

No statement dispute or node fault was found.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
