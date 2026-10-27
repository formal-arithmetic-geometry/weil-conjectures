## Worker report

The module `Sheaf.AlgebraicGeometry.RationalActionDomainLaws` states
`AlgebraicGeometry.existsUnique_rational_action_domain_laws`, with one `sorry` and
no new definitions. It states existence and uniqueness of the rational extension,
its maximal representative, and both pointwise domain laws. The node is unchanged
except for `lean`. No statement correction, new node, or dependency repair is needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Schemes over k | `G X Y : Over (Spec (.of k))` |
| All schemes separated and finite type | For each of G, X, Y: `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on its structure morphism |
| Smooth integral group scheme G, with identity e | `[GrpObj G] [IsIntegral G.left] [Smooth G.hom]`; `1 : 𝟙_ (Over (Spec (.of k))) ⟶ G` is the identity point |
| X integral | `[IsIntegral X.left]` (nonempty, reduced, irreducible) |
| Dense open subscheme Y of X | `j : Y ⟶ X`, `[IsOpenImmersion j.left]`, `hj : Dense (Set.range j.left)`; allowing any presentation of the open subscheme |
| Regular action a on Y, with unit and associativity | `[ModObj G Y]`, whose `smul`, `one_smul`, `mul_smul` are exactly these morphism data and identities |
| Products are scheme fibre products | `G ⊗ X`, `G ⊗ Y` use the canonical Cartesian monoidal structure on `Over`; their left schemes are `pullback G.hom X.hom`, `pullback G.hom Y.hom` |
| Rational map is an equivalence class of dense-open morphisms | `Scheme.RationalMap`, `Scheme.PartialMap`, `p.toRationalMap = α` |
| Unique rational extension | `∃! α : Scheme.RationalMap (G ⊗ X).left X.left, ...` |
| Largest domain of definition | `p.domain = α.domain`; Mathlib's `RationalMap.domain` is the union of the domains of every representative |
| The extension restricts to a followed by Y into X on all G × Y | `∃ i`, `i ≫ p.domain.ι = (G ◁ j).left`, and `i ≫ p.hom = (ModObj.smul ... ≫ j).left`; i is the factorization of the open inclusion through the maximal domain |
| k-points g, h, x | Morphisms from `𝟙_ (Over (Spec (.of k)))`; its left scheme is `Spec (.of k)` |
| If e·x is defined, it equals x | For every domain lift t of `lift 1 x`, `t ≫ p.hom = x.left` |
| Both h·x and g·(h·x) are defined | Domain lifts t, v of `lift h x`, `lift g y` with values y and z |
| (gh)·x is defined and equals g·(h·x) | `∃ w`, a domain lift of `lift (g * h) x` with `w ≫ p.hom = z.left` |

An open immersion is a monomorphism, so the domain lifts encode definedness
without extra choices or restrictions. A map from Spec k factors through an open
exactly when its image belongs to that open. The equality of the value morphisms
is equality of k-points, not merely equality of underlying topological points.
Every value of the maximal representative at a k-point is itself a k-point:
the action is over k on G × Y, and reduced-source/separated-target agreement
extends this equality to its maximal representative. Thus quantifying y and z
as k-points does not discard any defined successive actions. The maximal
representative is uniquely determined by its rational class, by the Mathlib
maximal-representative leaf. The unique rational extension is characterized by
its restriction on the dense open G × Y; the additional laws are its properties.

The node's sentences explaining normality and dimension introduce conventions;
no normality hypothesis, dimension variable, or dimension conclusion occurs in
this item. Accordingly there is no normality binder or artificial dimension clause.

Dependency interfaces read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (via imported field/scheme modules).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed
  part of the recorded algebraic-closure dependency. No algebraic closure of a
  second field is an object in this node.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`; these are
  publicly available through the recorded `Morphisms.Proper` import.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`, whose field
  says precisely that the diagonal is a closed immersion; publicly imported by
  `Morphisms.Proper`. The stronger predicate `IsProper` is not assumed.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`; the Cartesian specialization
  and group operations on points are in `Monoidal.Cartesian.Grp`. The recorded
  upstream `GroupScheme.Defs` documentation uses exactly this `Over` encoding.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies
  the canonical `CartesianMonoidalCategory` instance on `Over S`, using those
  pullbacks. `CartesianMonoidalCategory.lift` is the universal pair of maps.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` was read; no dimension
  occurs in the resulting signature, so no unused import is added for it.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `ModObj` with its full action signature
  and unit/associativity fields; `Monoidal.Cartesian.Mod` gives its Cartesian form.
- Proof dependency `lem-sfb-rational-map-maximal-representative` is already a
  Mathlib leaf: `Scheme.RationalMap.domain`, `toPartialMap`,
  `PartialMap.toPartialMap_toRationalMap_restrict`,
  `RationalMap.toRationalMap_toPartialMap`, and
  `PartialMap.equiv_iff_of_isSeparated_of_le`, all read in
  `Mathlib.AlgebraicGeometry.Birational.RationalMap` and available publicly since
  rational maps are in the statement itself.
- Proof dependency `lem-sc-scheme-over-field-universally-open` is a Mathlib leaf:
  the recorded `instUniversallyOpenOfIsIntegralOfSubsingletonCarrierCarrierCommRingCat`
  is in `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`, imported as a proof import.
- `lem-wf-affine-product-reduced` has no recorded Lean declaration or Mathlib match,
  so there is no proof module to import for it. Its role is preserved in the full
  natural-language proof docstring.

Edge cases checked: X and G cannot be empty by IsIntegral, and the dense open Y
cannot be empty; no unnecessary inhabitedness binder is added. Y = X, the trivial
group, and dimension zero are permitted. No characteristic restriction occurs.
The unit assertion is conditional, and no unconditional extension at (e,x) is
asserted. The composition clause does not assume that (gh,x) is already in the
domain. Non-normal integral X is permitted. k, schemes, and their point schemes
share arbitrary universe u; no independent lower-universe test objects occur.

Searches:

1. `msearch.py ... leanfinder "maximal domain of rational map action unit associativity algebraic group scheme"`:
   eight hits, including `RationalMap`, `compHom`, `exists_rep`, and `IsOver`;
   no action-domain theorem.
2. `msearch.py ... loogle "Scheme.RationalMap, AlgebraicGeometry.Scheme.RationalMap.domain"`:
   zero hits (unknown abbreviated identifier `Scheme.RationalMap`).
3. `msearch.py ... grep "RationalMap|rational map|PartialMap" AlgebraicGeometry`:
   twenty hits identifying Mathlib's Birational/RationalMap and composition modules.
4. `msearch.py ... leansearch "rational extension of regular group scheme action maximal domain unit composition"`:
   eight unrelated group-action/unitization/rational-function hits; no theorem.
5. Direct `rg` for `RationalMap|PartialMap` in `lean/WeilConjectures` and
   `lean/Sheaf`: generic inverse-partial-map restrictions and function-field
   interfaces, and unrelated coefficient rationalization; no matching action law.
   Direct searches for the item id and proposed theorem name found no collision.
   Direct Mathlib AlgebraicGeometry search for
   `rationalAction|rational_action|RationalMap.*action|action.*RationalMap` found none.
6. Read the existing categorical `ModObj` and Cartesian group-object APIs instead
   of adding a second action definition.

Source checked online: https://arxiv.org/html/1311.6060v2, Definition 4.2 and
Lemma 4.3, including the largest-domain convention and the exact direction of
both definedness implications. This agrees with the accepted node and its proof.
The example CompactObject module is withdrawn in the current clone; its node now
records the identical upstream `WeilConjectures.CategoryTheory.CompactObject`.

Validation: `scompile.py Q92 lem-sfb-rational-action-domain-laws <module>` passed
against the live server, 2.3 seconds, with no errors or unexpected warnings.
Its initial local attempt encountered `OSError(28, 'No space left on device')`;
the prescribed wrapper automatically confirmed the compile on the server and
returned exit 0. No compiler limit or tool was changed.

## Second reading by Q92

A second pass by this worker reread the node and the complete signature; no other
agent was started, as the dispatch brief forbids it. The maintainer performs the
independent review. Checked separately the three finite-type/separated structure
maps, smooth/integral G, integral X, the open immersion and dense image, and the
full ModObj action identities. Checked that `G ◁ j` is identity on G and j on Y;
the two factorization equations encode equality on all of G × Y. Checked that
`p.domain = α.domain` prevents a merely smaller representative. The final
existential w supplies the previously unassumed product-domain membership, and
its value is the same z obtained from the second lift v. The unit clause compares
whole scheme morphisms with x.left. No normality or positive-dimension assumption
has been introduced. The initial missing group-on-points scoped instance was
repaired by importing `Monoidal.Cartesian.Grp` and opening its existing scope;
there are no file-local definitions, notations, or instances. No mathematical
mismatch was found. All declarations are stage-2 statements with sorry only.

Delivery dry run: `deliver2.py Q92 lem-sfb-rational-action-domain-laws --no-push`
returned `OK (dry run): commit 74efe8a1c53 passes the preflight and compiles; nothing pushed`.
