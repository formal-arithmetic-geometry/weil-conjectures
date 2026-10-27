## Worker report

Item: `lem-sfb-ample-curve-two-section-pencil`, group Q16, stage 2, 2026-10-22.

The module `Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil` states
`AlgebraicGeometry.Scheme.Modules.exists_ample_curve_two_section_pencil` with `sorry`.
All nine auxiliary definitions have real data and implement objects already introduced in
this node: the orbit tensor bundle, its norm sections and the two coordinate morphisms.
No definition node or dependency repair is needed. No statement correction is made.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Any field F, including finite fields | `(F : Type u) [Field F]`, with no infinitude or characteristic hypothesis |
| Nonempty scheme Y over F | `(Y : Scheme.{u}) [Nonempty Y] (f : Y ⟶ Spec (CommRingCat.of F))` |
| Projective | `[IsHProjective f]`, the recorded finite projective-space embedding convention |
| Finite type | `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded conjunction |
| Topological Krull dimension at most one | `(hdim : topologicalKrullDim Y ≤ 1)` |
| Ample invertible module L | `(L : Y.Modules) [L.IsInvertible] (hL : IsAmple Y L)` |
| Finite group acting by F-automorphisms | `(G : Type v) [Group G] [Finite G] (ρ : G →* Aut Y)` and `(hρ : ∀ g, (ρ g).hom ≫ f = f)` |
| No faithfulness assumption | There is no injectivity or effective-action binder |
| B is the tensor product of all g*L | `pencilOrbitBundle (fun g ↦ ρ g) L`; `pencilGroupElements` enumerates every group element once and `pencilTranslateTensor` recursively tensors its actual `tensorPullback` modules |
| Norm in B^d using the canonical permutation | `pencilNormSection (fun g ↦ ρ g) L d s`; its section is the recursive tensor of canonical pullback sections, followed by `pencilTranslatePowerIso` into the actual `(pencilOrbitBundle ... L).tensorPow d` |
| Positive degree and ordinary sections | `∃ d : ℕ, 0 < d ∧ ∃ a b : (L.tensorPow d).sections` |
| Z(a) is the residue-zero locus | `(nonvanishingLocus (L.tensorPow d) (a.val (op ⊤)))ᶜ`; the recorded definition is germ membership in the maximal ideal times the stalk, equivalent to zero in the residue fibre |
| The two unions of inverse-translated zero loci are disjoint | `Disjoint (⋃ g : G, (ρ g).hom ⁻¹' (...)ᶜ) (⋃ g : G, (ρ g).hom ⁻¹' (...)ᶜ)` |
| a,b generate L^d | The existential proof `ha : Epi ((L.tensorPow d).freeHomEquiv.symm (pencilSectionPair ... a b))` |
| Both norm sections generate B^d | The analogous `hN : Epi (...freeHomEquiv.symm (pencilSectionPair ... (pencilNormSection ... a) (pencilNormSection ... b)))` |
| Both morphisms [a:b] and [N(a):N(b)] are finite | The first and second `IsFinite (pencilCoordinateMorphism ...)` conjuncts |
| The norm morphism is G-invariant | `∀ g : G, (ρ g).hom ≫ pencilCoordinateMorphism ... = pencilCoordinateMorphism ...`, an equality in Scheme, including structure sheaves and nilpotents |
| No smoothness, reducedness or irreducibility assumptions | None appears in the binders |

`M.sections` is Mathlib's compatible-family encoding of global sections. Evaluation at
`op ⊤` gives the ordinary section over Y. `pencilSectionPair` uses `ULift.{u} (Fin 2)`
to put the index type in the module coefficient universe; this has exactly two entries.
`pencilCoordinateMorphism` is a wrapper around the recorded
`ProjectiveSpace.homOfGeneratingSections`, with an explicit invertibility proof so the
conclusion can first supply it for the orbit tensor power. `hB` is an existential witness
of that power's invertibility, not an additional assumption. It follows from invertibility
of L under pullback and tensor product, as in step 7 of the node's proof.

Construction audit: `pencilTranslateSection` uses `tensorPullbackSectionAdjunction`, whose
unit is uniquely normalized by the actual pure tensor `1 ⊗ s`. Its explicit restriction
along `⊤ ≤ g⁻¹ ⊤` puts this in global sections. `pencilTranslatePowerIso` recursively
uses the existing `boundaryPullbackPowIso` and `tensorPowTensorObjIso`. The former is
constructed by the tensor-pullback/Mathlib-pullback adjunction comparison and the monoidal
pullback tensorator; the latter is the existing symmetric tensor-power distribution.
Thus the comparison is a specified composite of canonical maps, rather than an arbitrary
isomorphism or a choice from mere existence. The empty list uses only recursive unitors.
Finally `homOfGlobalSection` and `SheafOfModules.unitHomEquiv` convert the resulting top
section back to the compatible-family encoding. There are no `sorry`s inside data.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field` (`Mathlib/Algebra/Field/Defs.lean`).
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`.
- `def-weil-finite-type-morphism`: Mathlib
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim : WithBot ℕ∞`.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow`, `tensorPowTensorObjIso`.
- `def-weil-pbc-ample-invertible-module`: `WeilConjectures.AlgebraicGeometry.Ample`,
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and `nonvanishingLocus`.
- `def-pur-sheaf-tensor-product`: the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is publicly imported;
  its `SheafOfModules.cochainModulesMonoidal` specializes the same localization tensor
  to the Zariski scheme setting. The existing scheme tensor notation and tensor section
  operations are used, with no new tensor construction.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` and `tensorPullbackSectionAdjunction`.
- `def-weil-pbc-generating-sections`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`,
  `SheafOfModules.GeneratingSections`, specifically its `epi` predicate
  `Epi (M.freeHomEquiv.symm s)`.
- `def-weil-pbc-morphism-to-projective-space-by-sections`:
  `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`,
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`.

Also reused without duplication: `boundaryPullbackPowIso` from
`WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`,
`tmulSection` and `unitSectionsEquiv` from
`WeilConjectures.AlgebraicGeometry.Modules.TensorSection`, and `homOfGlobalSection`
from `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`.
These are canonical constructions already available upstream; the first requires no
square-zero, immersion, or invertibility hypothesis.

The stated proof dependencies are imported in plain visibility, including the recorded
modules for finite-set affine section neighbourhoods, zero-dimensional finite closed sets,
invertible pullback/tensor fibres, the generating-section fibre criterion, projective-space
functor of points and standard charts, and projective-implies-proper. The Mathlib leaves
are supplied by Noetherian, Proper and their imports. `lem-sfb-affine-proper-finite` has no
recorded declaration yet, so has no module to import; its step remains in the proof docstring.
The main theorem's docstring carries all ten proof steps, with their DAG references.

Edge cases checked mathematically before drafting:

- Dimension zero, e.g. `Y = Spec F`: constant coordinate maps are finite because Y is
  finite over F, so neither dimension exactly one nor surjectivity onto P¹ is asserted.
- Finite F and every characteristic: 09NV handles finite sets of scheme points and the
  proof never needs an F-rational point in a parameter open.
- Trivial G and nonfaithful actions: the enumeration still lists all elements; no quotient
  by the kernel and no distinctness of the translated automorphisms is required.
- G is nonempty as a group; the helper product nevertheless defines the empty-list base
  case as the actual structure module and its section 1.
- Reducible, disconnected and nonreduced Y: the dimension bound is topological, generation
  is a sheaf epimorphism, and invariance is equality of scheme morphisms. No reducedness
  or component smoothness is imposed.
- Empty zero locus of a or b is allowed. A zero section on a positive-dimensional component
  cannot yield a finite constant pencil, but the theorem only asserts suitable witnesses.
- The degree-zero case is excluded exactly by `0 < d`; helpers still define its tensor
  comparisons without partial data.
- The group universe `v` is independent of scheme/coefficient universe `u`, so an arbitrary
  finite group is not accidentally restricted by size.

Searches for an existing statement / constructions:

1. `msearch.py ... leanfinder` with query "Orbit-separated two global sections of an ample
   line bundle on a projective curve over a field yielding a finite invariant map to
   projective line": eight hits, principally `AlgebraicGeometry.Proj.fromOfGlobalSections`
   and unrelated Weierstrass point declarations; none is this theorem.
2. `msearch.py ... loogle` with query
   `AlgebraicGeometry.Scheme.Modules.IsAmple, AlgebraicGeometry.IsFinite`: zero hits;
   remote Loogle does not know the project `IsAmple` declaration.
3. `msearch.py ... grep 'normSection|two_section|pencil|tensorNorm' AlgebraicGeometry`:
   zero Mathlib hits.
4. `rg` in the project's `lean/WeilConjectures`, `lean/Sheaf` and `dag/nodes` for
   `normSection|tensorNorm|orbit.*(Section|Tensor)|two.section.pencil|two_section_pencil`
   found no existing norm-section construction or theorem. It found the consumer
   `InvariantLocalCurvePencils.lean`, where the node is mentioned in a proof docstring;
   that module does not define the norm or this statement.
5. `grep -rn 'lem-sfb-ample-curve-two-section-pencil' lean/WeilConjectures`: no hits.
6. Searches for `tensorPow`, pullback/tensor comparison and tensor sections located the
   actual existing comparisons and `tmulSection` used above. A search for unit tensor
   powers found no public recursive unit-power-removal constructor to reuse here.
7. Exact-name searches for `pencilUnitPowerIso`, `pencilOrbitBundle`, `pencilNormSection`
   and `exists_ample_curve_two_section_pencil` in Mathlib/project declaration records
   and both source roots found no collision.

Source check: read Stacks `coherent.tex`, `lemma-kill-by-twisting` (02O1), and read the
publisher PDF [de Jong, §3.4, p.606](https://www.numdam.org/item/10.5802/aif.1575.pdf).
The paper supplies the special-fibre finite-pencil input. The node explicitly strengthens
it to orbit-separated zero loci using the finite-set affine neighbourhood argument.
The Lean follows that node without adding the paper's global relative-family setting.

Compilation: prescribed `scompile.py Q16 lem-sfb-ample-curve-two-section-pencil <module>`
completed successfully against the live server build (sandbox and library module checks,
8.3 s and 7.0 s on the reported run), with no unexpected warning or error.

No STATEMENT-DISPUTED issue, hollow datum, or unusable statement dependency was found.

## Second reading by Q16

This dispatcher assignment has one worker and forbids starting other agents. The independent
reading is therefore the maintainer's review, as specified in the brief; this section does
not claim another worker read the file. A separate self-audit with the node and full Lean
open checked the above correspondence again. In particular, it checked that the norm lives
in the actual B tensor power, both pairs have epimorphic free-sheaf maps, BOTH maps are
finite, and invariance is an equality of scheme morphisms. The extra existential hB is an
invertibility witness used by the coordinate API and imposes no hypothesis on the input.
No mismatch requiring a node statement change was found.
