## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.BorelHomomorphismRigidity` states
`AlgebraicGeometry.hom_ext_of_borel_baseChange` with its proof exactly `by sorry`.
It introduces no definitions, helper theorems, or new nodes. The item's only changed
field is `lean`; its mathematical statement, dependencies and proof plan are unchanged.

Source checked directly: Milne, Algebraic Groups (2017), Proposition 17.21,
printed p.358 (PDF p.370), including its general-k-algebra paragraph. This paragraph
constructs the coset-invariant difference map on every R-algebra and uses
Γ((G/B)_R,O) = R tensor_k Γ(G/B,O). The next proposition uses this full R-form
for inner automorphisms. The theorem therefore cannot be replaced by a theorem
only over k or by agreement on k-valued points.

Hypothesis and conclusion matching:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| k-group schemes G,H and B | `(G H B : Over (Spec (.of k))) [GrpObj G] [GrpObj H] [GrpObj B]` |
| G smooth | `[Smooth G.hom]` |
| G connected | `[ConnectedSpace G.left]`, whose definition includes nonemptiness |
| G affine | `[IsAffine G.left]` |
| G of finite type | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| H smooth | `[Smooth H.hom]` |
| H connected | `[ConnectedSpace H.left]` |
| H affine | `[IsAffine H.left]` |
| H of finite type | `[LocallyOfFiniteType H.hom] [QuasiCompact H.hom]` |
| B is a Borel included in G | `(i : B ⟶ G) (hB : IsBorelGroupScheme i)` |
| B closed, smooth, connected, solvable and maximal | Exactly the existing conjunction and factorization maximality in `IsBorelGroupScheme`; its closed-subgroup class includes `IsMonHom i` |
| Every commutative k-algebra R | `(R : Type u) [CommRing R] [Algebra k R]` |
| G_R and H_R | `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj G` and the same expression with H |
| f₁,f₂ are R-group-scheme homomorphisms | They are morphisms in `Over (Spec (.of R))` between these pullbacks, with `[IsMonHom f₁] [IsMonHom f₂]` |
| Restrictions to B_R agree as scheme morphisms | `h` equates the `.left` scheme morphisms of `(Over.pullback ...).map i ≫ f₁` and the analogous composite for f₂ |
| Equality as R-group-scheme morphisms | `f₁ = f₂` in the slice category; homomorphism compatibility is propositional structure |
| R need not be reduced; no reductivity or characteristic assumption | No such binders are present; in particular there is no `Nontrivial R` |

The scalar extensions and the restriction map are the existing canonical
`CategoryTheory.Over.pullback` functor. Its object is definitionally
`Over.mk (Limits.pullback.snd G.hom (Spec.map ...))`, so its underlying scheme is
precisely G ×_k Spec R, not an arbitrary model. The scoped instance
`CategoryTheory.Functor.grpObjObj` gives its canonical group operations from the
monoidal pullback functor. `open scoped CategoryTheory.Obj` selects an existing
exported instance, and creates neither a local instance nor a second group structure.
The map on i is the canonical pullback map. All universes and variables are explicit,
with `set_option autoImplicit false` enforced. The fixed ambient universe contains
k, the schemes and arbitrary test algebras, following the dependency interfaces.

Dependency declarations read and used (directly or through public imports):

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic;
  the node's Mathlib match explicitly names this algebraically-closed-field predicate.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom`,
  Mathlib.CategoryTheory.Monoidal.Grp and Mathlib.CategoryTheory.Monoidal.Mon;
  the specialization to `Over (Spec k)` is documented in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-sfb-borel-subgroup-scheme`: `AlgebraicGeometry.IsBorelGroupScheme`,
  Sheaf.AlgebraicGeometry.GroupScheme.Borel. Read its complete definition,
  including the maximality quantifiers over larger smooth connected solvable subgroups.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, used by the Borel predicate.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, as used in
  `CategoryTheory.Over.pullback` (Mathlib.CategoryTheory.Comma.Over.Pullback).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme.
- Affineness is Mathlib's `AlgebraicGeometry.IsAffine` in
  Mathlib.AlgebraicGeometry.AffineScheme, already available from the dependencies.
- Canonical group transport: `CategoryTheory.Functor.grpObjObj` and
  `CategoryTheory.Over.pullback`, with the monoidal structure from
  Mathlib.CategoryTheory.Monoidal.Cartesian.Over. Its `grpObjMkPullbackSnd`
  corroborates that these are the standard pullback group structures.

All currently stated proof dependencies are imported without `public`:
`exists_homogeneousQuotient`, `Scheme.proper_reduced_globalSections_product`,
`Scheme.Modules.H.baseChange_bijective_of_isSeparated`,
`RingedSpace.openCohomologyZeroSectionsIso`, `Scheme.Modules.H.baseChange`,
Mathlib's fpqc subcanonical topology, flatness over a field, `ΓSpec.adjunction`
and `pullbackSpecIso`, using their recorded modules.
`lem-sfb-borel-quotient-proper-geometry` has no Lean record or upstream closed
declaration yet, so there is no module to import for that proof prerequisite.
It is retained explicitly in the theorem's complete six-step proof docstring.
No statement dependency needs a repair or a new definition.

Edge cases checked before writing and on rereading:

- R = k recovers Milne's first case; the statement also includes all other k-algebras.
- Nonreduced R, for example k[ε]/ε²: equality is equality of full scheme maps;
  no restriction to reduced points, geometric points, or rational points occurs.
- R = 0: `CommRing R` and `Algebra k R` permit the zero algebra, so the empty
  scalar extensions and their unique morphisms are included.
- B = G, including connected solvable G and the trivial group: restriction is
  along a presentation of the entire subgroup, giving the expected equality.
- G = SL₂ with its triangular Borel: G need not be solvable, and the existing
  Borel predicate has precisely the required maximal connected solvable meaning.
- Noncommutative H and positive characteristic: no commutativity, reductivity,
  characteristic-zero, separability, surjectivity or kernel condition was added.
- Empty G or H over k is excluded by the node's connectedness condition, not by
  an added assumption; emptiness after R = 0 remains allowed.

Searches performed with the prescribed wrapper and direct source reads:

- msearch LeanFinder: `Homomorphisms of smooth connected affine algebraic groups
  agreeing on a Borel subgroup are equal after arbitrary algebra base change`:
  eight hits, including `AffineSpace.hom_ext`, `ext_of_isAffine`, normalization
  extensionality and formally unramified lifts; none asserts Borel restriction rigidity.
- msearch Loogle: `IsBorelGroupScheme, IsMonHom`: zero hits; unknown identifier
  `IsBorelGroupScheme` because this is a project definition, not a Mathlib one.
- msearch LeanSearch: `Two algebraic group homomorphisms equal on a Borel subgroup
  are equal over every base algebra`: eight abstract algebra/group extensionality
  hits (`AlgHom.ext`, `GrpCat.Hom.ext_iff`, etc.); no match.
- msearch grep: `Borel|borel|homomorphism.*rigid` in Mathlib/AlgebraicGeometry:
  zero hits.
- Direct `rg` for `Borel|borel|homomorphism.*rigid` in
  lean/WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry:
  found the Borel definition and supporting group-theory statements, no rigidity theorem.
- `grep -rn 'lem-sfb-borel-homomorphism-rigidity' lean/WeilConjectures`: no hits.
- Direct `rg` for `borel.*hom|hom.*borel|Borel.*rigid` throughout lean/Sheaf,
  lean/WeilConjectures and dag/lean_names_upstream.json: no existing matching declaration.
- Direct `rg` for `hom_ext_of_borel_baseChange` in Mathlib, both project Lean
  trees and dag/lean_names_upstream.json: the chosen name was absent before writing.
- Read the distinct DAG node `lem-sfb-homomorphism-borel-rigidity`: it has no Lean
  declaration and states only the R = k form; it cannot supply this arbitrary-R item.

Validation: prescribed scompile.py compiled both its sandbox and library views
successfully (3.1 s and 2.1 s), with no errors or warnings. The named theorem is
intentionally unproved, as required for stage 2. No statement dispute or node fault.

## Second reading by Q16

A separate in-session reading compared the saved node's unchanged statement with
the saved Lean signature and the definitions it uses. No second agent was started,
as the dispatcher brief explicitly prohibits it; the maintainer reviews independently.

The checks revisited each row above, especially finite type as both local finite
type and quasi-compactness for G and H; full maximal smooth connected solvable
closed-subgroup semantics through `IsBorelGroupScheme`; and `.left` equality of
restrictions as scheme maps. They confirmed that f₁,f₂ use the canonical group
structures on the actual fibre products over Spec R, rather than a supplied
arbitrary group structure. The conclusion is equality in `Over (Spec R)`.
No `Reduced R` or `Nontrivial R` assumption appears, so nilpotent and zero
algebras survive this reading. No mathematical mismatch or correction was found.
The theorem docstring follows all six DAG proof steps and names their inputs.
