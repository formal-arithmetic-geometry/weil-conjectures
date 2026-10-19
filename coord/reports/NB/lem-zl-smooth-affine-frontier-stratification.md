## Worker report

The module `Sheaf.DeligneLaumon.SmoothAffineFrontierStratification` states
`WeilConjectures.smooth_affine_frontier_stratification`.  It uses the recorded finite-field
 datum `WeilConjectures.FiniteFieldDatum`, the finite locally closed scheme stratification
interface, Mathlib's scheme morphism properties, and the categorical finite-field base-change
functors.  No definition with the requested frontier-refinement statement exists in Mathlib,
the source repository, or `lean/Sheaf`.

The hypotheses and clauses are rendered as follows.  `D : FiniteFieldDatum` supplies the
prime-power fields `D.k₀`, `D.k`, and `D.extensionSubfield m hm`; `a₀` is the structure map
of the separated finite-type scheme `X₀`, with `IsSeparated`, `LocallyOfFiniteType`, and
`QuasiCompact` instances.  `T` is a finite locally closed stratification of
`(D.geometricFiber (Over.mk a₀)).left.nilradical.subscheme`, and `hTred` states that every
`T.domain i` is reduced.  The conclusion chooses `m ≥ 1`, sets `km`, `Sm`, `Xm`, `X`, and
the base-change functor `BC`, and supplies a comparison isomorphism `χ : BC.obj Xm ≅ X`.

The chain is `t : ℕ` and `Z : Fin (t + 1) → Over Sm`; every `Z a` is reduced.  The
existential proofs `hZ0` and `hZt` identify `Z 0` with the nilradical reduction of `Xm`
and `Z (Fin.last t)` with the empty `Sm`-scheme.  The maps
`ι a : Z a.succ ⟶ Z a.castSucc` are closed immersions, and the maps
`z a : Z a ⟶ Xm` satisfy the reduction inclusion at index zero and
`z a.succ = ι a ≫ z a.castSucc`, so all chain maps are over the same `Sm`.

For each `a : Fin t`, `u a : U a ⟶ Z a.castSucc` is an open immersion and its range is the
complement of the range of `ι a`, rendering `U a = Z a \ Z (a+1)`.  The finite family is
indexed by `Fin (r a)`.  Each `V a b` is nonempty, reduced, affine, and geometrically
connected; `d a b : ℕ` and `SmoothOfRelativeDimension (d a b) (V a b).hom` render the
constant relative dimension (a natural number is automatically nonnegative).  The map
`v a b : V a b ⟶ U a` is both open and closed, the union of its ranges is all of `U a`,
and distinct ranges are disjoint.  If `d a b = 0`, the `Over Sm` isomorphism to
`Over.mk (𝟙 Sm)` renders `V a b ≅ Spec km` over the same finite field.

Finally, for each component there are `ν` and an immersion `j` into `T.domain ν` such
that, after composing with `T.immersion ν` and the canonical reduction immersion, it
agrees with the geometric base change of `v a b ≫ u a ≫ z a.castSucc` under `BC` and
`χ`.  Thus the geometric base change is a locally closed subscheme contained in one
prescribed `T_ν`.  All chain and component maps and the displayed zero-dimensional
isomorphism are morphisms in `Over Sm`; `χ` is the base-change comparison used to identify
the finite-subfield model with the fixed geometric fibre.

The statement was checked on the empty case (`t = 0`, forcing the reduced fibre to be
empty), on the nonempty case (each `Fin (r a)` component is nonempty), and on relative
dimension zero.  The complement and disjointness clauses are set-theoretic images of the
corresponding open/closed immersions, while the `Over Sm` types retain the common field of
definition.

Dependency declarations used:

* `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum` and its
  `extensionSubfield`, `extensionEmbedding`, and `geometricFiber` declarations.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper` (the
  recorded proper-morphism Mathlib match).
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` (the
  recorded finite-type Mathlib matches).
* `Sheaf.AlgebraicGeometry.BaseChangeConventions` and its recorded base-change
  conventions (`AlgebraicGeometry.Scheme.Modules.moduleBaseChange` and related
  declarations), together with `CategoryTheory.Over.pullback`.
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
* `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`/`Subscheme`,
  `AlgebraicGeometry.Scheme.nilradical`, `IdealSheafData.subscheme`, and
  `IdealSheafData.subschemeι`.
* `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension` and `AlgebraicGeometry.Smooth`.
* `Mathlib.AlgebraicGeometry.Geometrically.Connected`,
  `AlgebraicGeometry.GeometricallyConnected`.
* `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `AlgebraicGeometry.IsAffine`.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
* `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
* `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `AlgebraicGeometry.IsImmersion`.
* `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom`.

Searches for an existing declaration were made with:

* `msearch.py ... leanfinder "finite smooth affine frontier stratification of a finite type
  scheme over an algebraic closure of a finite field refining a finite locally closed
  partition and descending to a finite subfield"`: only generic affine-cover and limit
  declarations; no matching frontier-stratification theorem.
* `msearch.py ... loogle "AlgebraicGeometry.FiniteLocallyClosedStratification,
  AlgebraicGeometry.GeometricallyConnected, AlgebraicGeometry.SmoothOfRelativeDimension,
  Over.pullbackComp"`: no hit (the finite stratification interface is project-specific).
* `msearch.py ... grep "smooth.*affine.*frontier|frontier.*stratification"
  Mathlib/AlgebraicGeometry`: no hits.
* `rg` over `WeilConjectures` and `lean/Sheaf` for the item id and the same frontier terms:
  no existing declaration; only the finite stratification support modules were found.
* The node's recorded LeanSearch, Loogle, LeanFinder, and Mathlib grep searches were also
  read; each reports no exact match.

The file compiles with `scompile.py` and has no errors or warnings.  No `STATEMENT-DISPUTED`
condition or node fault was found.

## Second reading by NB

I reread the node and the complete module after compilation.  The finite-field datum,
separated finite-type hypotheses, reduced partition, common `m`, reduced closed chain,
open differences, nonempty smooth affine geometrically connected pieces, constant natural
relative dimensions, zero-dimensional `Spec km` clause, common-field maps, and containment
in a prescribed reduced stratum each have a corresponding Lean binder or conjunct.  The
empty chain is represented by `t = 0`; no Frobenius-stability hypothesis appears.  The only
auxiliary datum is `χ`, the base-change comparison identifying the iterated finite-field
pullback with the fixed geometric fibre; it is used solely to express the canonical
geometric-base-change containment.  No mismatch was found and no change was needed.
