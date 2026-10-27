## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcCartierIdealReflection` states
`AlgebraicGeometry.fpqc_cartier_ideal_reflection` with proof `sorry`. It introduces
no definitions or helper theorems. The item's `lean` field is supplied and
`stmt_deps` gains the existing definition nodes owning the canonical structure-sheaf
map and finite local freeness of fixed rank.

Hypothesis and conclusion correspondence:

- The base scheme X and closed subscheme T are `{X T : Scheme.{u}}`; the specified
  closed immersion is `(i : T ⟶ X) [IsClosedImmersion i]`.
- The specified quasi-coherent kernel ideal I is exactly `i.ker`, its underlying
  module is `i.ker.toModules`, and its inclusion is `i.ker.toModulesι`. There is
  no independent ideal variable, chosen subobject or arbitrary inclusion.
- The family is `{A : Type w} (Y : A → Scheme.{u}) (g : ∀ a : A, Y a ⟶ X)`.
  Universes u and w are explicit and independent; the index type may be empty.
  `hg : Presieve.ofArrows Y g ∈ Scheme.fpqcPrecoverage X` is precisely the
  recorded fpqc-covering notion, including flatness and quasi-compact covering.
- T_a is `pullback i (g a)`, q_a is `pullback.snd i (g a)`, and the specified
  kernel ideal J_a is `(pullback.snd i (g a)).ker`.
- The hypothesis that every J_a is an effective Cartier ideal is
  `hJ : ∀ a : A, (pullback.snd i (g a)).ker.IsInvertible`.
  The recorded upstream ideal predicate `Scheme.IdealSheafData.IsInvertible`
  means local nonzerodivisor generators on affine neighbourhoods. It is the
  existing declaration of BOTH `def-nagata-effective-cartier-ideal` and
  `def-nagata-invertible-ideal`, and agrees with the current blueprint's
  `def-nagata-invertible-ideal.md` in `literature/blueprint/latest/`.
- The first conclusion, for every a, gives an isomorphism e from
  `(Scheme.Modules.tensorPullback (g a)).obj i.ker.toModules` to the actual
  kernel-ideal module `(pullback.snd i (g a)).ker.toModules`.
  The equality `e.hom ≫ ...toModulesι = ...map i.ker.toModulesι ≫
  Scheme.Modules.tensorPullbackObjUnitToUnit (g a)` ensures identification by
  the CANONICAL map into O_{Y_a}, retaining the specified inclusion. A bare
  abstract isomorphism of line bundles would not suffice. Since the ideal
  inclusion is monic, this equality also uniquely determines the factorization.
- `i.ker.toModules.IsFiniteLocallyFreeOfRank 1` renders local freeness of rank
  one. For fixed finite rank 1 this is exactly local freeness of rank one,
  without imposing any extra finite-presentation assumption on X or i.
- `i.ker.IsInvertible` renders the invertible-ideal AND effective-Cartier-ideal
  conclusion: the two recorded dependency nodes use this same predicate. The
  explicit module-rank conclusion also supplies the older module formulation
  of invertibility in the DAG text. No duplicated tautological conjunct is used.
- No reducedness, Noetherianity or etaleness assumptions appear. No global basis
  or compatible local bases are assumed or concluded.

Dependency declarations read and used (full signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  made available through the public imports.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`, including its
  affine-kernel characterization `Hom.ker_apply`; made available transitively.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  `pullback.snd`; available through the scheme closed-immersion imports.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`, exactly the effective Cartier predicate.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded
  module-pullback dependency, retaining the upstream `Scheme.Modules.tensorPullback`
  from `WeilConjectures.AlgebraicGeometry.TensorPullback` by public import.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules` and `toModulesι`.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `Scheme.Modules.tensorPullbackObjUnitToUnit`, the adjoint of the actual
  structure-sheaf map under the section-normalized tensor adjunction.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.

All stated proof dependencies have plain imports:
`WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`
(`closedSubscheme_baseChange_ideal_image`),
`Sheaf.AlgebraicGeometry.IdealTensorPullbackComparison`
(`existsUnique_idealTensorPullbackComparison`), and
`WeilConjectures.AlgebraicGeometry.Descent`
(`isFiniteLocallyFreeOfRank_of_toDescentData_iso` and its quasi-coherent form).
The four proof steps are included in the theorem docstring. Source text read:
Stacks descent.tex, `lemma-finite-locally-free-descends` (05B2) and
`proposition-fpqc-descent-quasi-coherent` (023T); divisors.tex,
`lemma-characterize-effective-Cartier-divisor` (01WS).

Edge cases checked before writing:

- Unit ideal: the empty closed subscheme has kernel O_X; 1 is a nonzerodivisor,
  so both the hypothesis and conclusion allow it.
- Empty covering: the fpqc-covering condition forces X empty; the rank-one and
  local-generator conditions are vacuous. No `Nonempty A` is imposed.
- Empty base and all empty family members are included. Over a nonempty base,
  an entirely empty family cannot satisfy the covering hypothesis.
- Identity closed immersion on a nonempty scheme gives the zero ideal, which
  is not an effective Cartier ideal. Joint surjectivity prevents the covering
  hypothesis from incorrectly making this an allowed nonempty example.
- Nonreduced base, e.g. a polynomial ring over a ring with nilpotents: a
  polynomial variable is still a nonzerodivisor; no reducedness is needed.
- Arbitrary flat, non-etale covers and non-Noetherian bases are allowed.
  Flatness is essential to the tensor-to-extended-ideal isomorphism and is
  supplied by `hg`, not silently added as a separate hypothesis.

Searches for an existing statement, 2026-10-24:

- `msearch.py ... leanfinder` query: "An ideal sheaf is an effective Cartier ideal
  if its base changes to an fpqc covering are effective Cartier ideals".
  Eight hits, all `Scheme.IdealSheafData` constructors or affine-ideal APIs:
  `IdealSheafData`, `mkOfMemSupportIff_ideal`, `ofIdealTop`, `ofIdeals`,
  `mkOfMemSupportIff`, `ideal`, `ideal_ofIdeals_le`, `mk.inj`; no matching theorem.
- `msearch.py ... loogle` query: `"FaithfullyFlat", "IsInvertible"`:
  successful service response, zero hits.
- `msearch.py ... grep` query:
  `Cartier|cartier|[Ii]nvertible.*[Dd]escen|[Dd]escen.*[Ii]nvertible`,
  subdirectory `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch` query: "Faithfully flat descent of locally free
  rank one ideal sheaves on schemes". Eight ring/module flatness hits,
  including `Module.Flat.of_flat_tensorProduct`, `RingHom.FaithfullyFlat`,
  `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` and
  `Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top`; no scheme ideal theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for this item's id and
  fpqc/Cartier/reflection combinations found only a proof-docstring reference
  in `Sheaf.AlgebraicGeometry.AffineSaturationCartierBoundary`, not a declaration.
  Broader reads of `Descent`, `IdealTensorPullbackComparison`, and
  `ClosedSubschemeBaseChangeIdealImage` found the separate ingredients already
  recorded as proof dependencies, not this combined statement. The chosen
  declaration name has no existing hit.

No statement dispute or correction, new nodes, or dependency repairs were needed.
The prescribed server `scompile.py` compiled this module cleanly in both its
sandbox and library import contexts (3.3 s and 10.6 s respectively), with no
errors or unexpected warnings. Both automatic-implicit options are disabled.


## Repair of return 617f6a87d8c4

H2 repaired: added `def-sfb-tensor-pullback-structure-sheaf-map` to the
item's `stmt_deps`. This existing definition node records exactly
`AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit`, in
`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`, already
publicly imported and used in the approved Lean statement. I read its node
and the recorded declaration with its docstring: the map is the inverse
canonical adjunction Hom bijection applied to the structure-sheaf map.
It supplies precisely epsilon in the identification equation.

This is the permitted addition of an already landed definition node under
brief-stage2 section 5 (STMT_DEPS MAY GAIN LANDED NODES), also explicitly
requested by the return. The node's existing text already states the
canonical map into the structure sheaf, so no mathematical statement
correction or section 1(C) change is needed. The TeX statement, proof,
proof dependencies, Lean module, and verbatim Lean signature are unchanged.
The advisory about declaration ownership of `toModulesι` requests no change;
the specified inclusion continues to use its existing upstream construction.

Compared the retained returned delivery against the current read-only main
node before editing: its only differing field was `lean`. After this repair
the only differing fields are `lean` and the requested `stmt_deps` addition.
The delivery wrapper refreshes the base and rebases the delivery through its
normal temporary-worktree bookkeeping; no direct git operation is used.


## Repair of return d792dbf6f9de

H2 repaired as requested: added `def-amb-finite-locally-free-module` to
`stmt_deps`. Its existing declaration is
`SheafOfModules.IsFiniteLocallyFreeOfRank` in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
already publicly imported by the unchanged Lean module. I read the owner
node and the declaration's full signature, definition, and docstring.
Specializing this predicate to `i.ker.toModules` and rank 1 is exactly the
conclusion's locally free rank-one condition. The extra local-generators
index universe does not impose a mathematical restriction, as confirmed
by the maintainer's `LocalGeneratorsData.shrink` review.

The previous repair adding
`def-sfb-tensor-pullback-structure-sheaf-map` is retained. This repair changes
only `stmt_deps` and this report relative to the returned delivery. TeX,
proof, proof dependencies, Lean source, and `lean.statement` are unchanged.
The Lean SHA256 remains
`4bf68d930cef84d39102d5aaf61dab0364517191c6063894574c5b52680a2f62`.
No statement correction is needed: the existing node text already states
local freeness of rank one. Section 5 of the standing brief permits adding
an already landed dependency with a Lean record, and this exact addition
is requested by the maintainer.

Compared the retained sandbox against current read-only main: before the
repair, only `lean` and the prior `stmt_deps` addition differed. The new
delta adds precisely the rank-predicate owner. The normal delivery wrapper
refreshes the base and reconstructs the delivery on current main; no direct
git command or write to the shared clone is used.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
