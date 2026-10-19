## Worker report

The module `Sheaf.AlgebraicGeometry.ToricRealizationFiniteType` states
`AlgebraicGeometry.Monoscheme.toric_realization_finite_type`, with its proof `sorry`.
It also gives two transparent, fully constructed abbreviations, `torusGroup` and
`coordinateTorusGroup`, bundling the existing torus and the standard Laurent coordinate
torus with Mathlib's canonical Hopf-algebra group structures. No independent notion,
new DAG node, dependency repair, or change to the natural-language statement is needed.

The sandbox from the earlier attempt had two Lean files but no node copy or report,
so the requested initial dry run was not yet possible. I retained the main file and
retained the earlier experiment as `Check.lean.txt` outside the deliverable module tree.
I read the current node, every statement dependency and its recorded declaration,
the proof dependencies and their available statements, and the ILO source. In the PDF,
printed pp.98--103 are PDF pages 104--109 and printed pp.104--106 are PDF pages 110--112.
Remark 3.1.4 describes finite monoid spectra and the generic stalk; Remark 3.1.10(ii)
gives the component decomposition; Proposition 3.2.2 gives realization by localization
gluing; 3.2.4 identifies the component's dense torus and its action. Section 3.2.19
uses the smooth torus action for characteristic-zero desingularization, including k=Q.
The node is a supporting statement, not the blueprint unit's own statement.

Every hypothesis and conclusion is rendered as follows. In this table `q` abbreviates
`ULift.{u} ℚ` only for explaining the file: the Lean statement contains the full term,
with no file-local notation, let binders, hidden `show`, or implicit universes.

| Node clause | Lean rendering and meaning |
| --- | --- |
| Fine monoscheme M with a finite affine cover | `(M : Fine.{u})`; the imported `Fine` structure contains its finite chart cover. An empty cover is allowed. |
| Torsion-free stalk group completions | `(hM : Fine.IsTorsionFree M)`, using precisely the recorded definition. |
| X=Q[M] with its specified structure map | `realization q M` and `realizationToBase q M`, the imported localization colimit and its canonical map. |
| X reduced | `IsReduced (realization q M)`. |
| X finite type over Q | `LocallyOfFiniteType (realizationToBase q M) ∧ QuasiCompact (realizationToBase q M)`. |
| Finitely many connected components | `Finite (ConnectedComponents (realization q M).carrier)`. |
| Each component integral | Every ambient connected component `D` is the range of an actual `componentι q C`, and every `componentRealization q C` satisfies `IsIntegral`. The range equality identifies its inherited open subscheme with that connected component; it does not replace components by arbitrary integral schemes. |
| On each component, generic L finite free of finite rank r | For every `C : ToricComponent M`, `∃ r : ℕ, Nonempty (C.lattice ≃* Multiplicative (Fin r → ℤ))`. A multiplicative equivalence to the finite integer-coordinate group is exactly a finite integral basis. The imported lattice is the completion of the component's generic stalk. |
| T=Spec Q[L] isomorphic as a group scheme to Gm^r | `Nonempty (torusGroup q C ≅ coordinateTorusGroup q r)` is an isomorphism in `Grp (Over (Spec (.of q)))`, not just in schemes. Both abbreviations use Mathlib's canonical `GrpObj` on Spec of the corresponding group algebra. |
| Coordinate multiplication and unit one | `coordinateTorusGroup` uses `MonoidAlgebra q (Multiplicative (Fin r → ℤ))`, the Laurent monomial algebra. The canonical Hopf structure sends `e^v` to `e^v ⊗ e^v`, with counit `e^v ↦ 1`. For a standard coordinate exponent vector this gives coordinate multiplication and identity coordinate one. No group law is chosen existentially. |
| T smooth finite-type over Q | `Smooth (torusToBase q C)`, `LocallyOfFiniteType (torusToBase q C)`, and `QuasiCompact (torusToBase q C)`. |
| T acts on that component by the indicated coaction | `IsCanonicalTorusAction q C (torusAction q C)` fixes the map by the dependency's chart formulas. The existential `action : ModObj (torusGroup q C).X (Over.mk (componentToBase q C))` with `action.smul.left = torusAction q C` states that this very map lies over Q and satisfies unit and associativity. `ModObj` uses the canonical group-algebra multiplication, not an arbitrary action. |
| Every reduced finite-type Q-scheme Y | `(Y : Scheme.{u}) (fY : Y ⟶ Spec (.of q))` followed by `IsReduced Y → LocallyOfFiniteType fY → QuasiCompact fY →`. The explicit structure map is needed to form the specified fiber product. |
| T×Q Y reduced | `IsReduced (pullback (torusToBase q C) fY)`. |
| T×Q Y finite type over Q | `LocallyOfFiniteType (pullback.snd (torusToBase q C) fY ≫ fY)` and `QuasiCompact` of the same composite structure map. These are properties over Q as stated in the node. |
| Projection to Y smooth and surjective | `Smooth (pullback.snd (torusToBase q C) fY)` and `Surjective` of that same second projection. |
| Finite disjoint unions reduced, finite type, finitely many components | For `n : ℕ`, `N : Fin n → Fine.{u}` and each summand torsion free, the scheme coproduct has `IsReduced` and finite `ConnectedComponents`; its canonical `Sigma.desc (fun i ↦ realizationToBase q (N i))` is locally finite type and quasi-compact. It is not an unspecified existential structure map. |

The universe variable `u` is explicit. `ULift.{u} ℚ` has the canonical lifted field
structure from `Mathlib.Algebra.Field.ULift`; it is the same rational field, with its
canonical rational scalar action, at the size required by the recorded realization
interface. This includes u=0 and does not restrict the sizes of monoschemes to Type 0.

Dependency declarations used, with their recorded modules:

- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`:
  `AlgebraicGeometry.Monoscheme.Fine`, `Fine.IsTorsionFree`, `ToricComponent`,
  `ToricComponent.lattice`, `realization`, `realizationToBase`,
  `componentRealization`, `componentι`, `componentToBase`, `torus`, `torusToBase`,
  `IsCanonicalTorusAction`, and `torusAction`. I read their complete signatures and
  docstrings in the current shared source. The existing coaction and its unique
  chartwise gluing are reused without replacement.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`,
  `AlgebraicGeometry.IsIntegral`; section-wise reducedness and integral domains on
  nonempty opens are the recorded equivalent formulations of the stalk/affine ones.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, and the associated
  `ConnectedComponents` quotient, with empty spaces having no connected components.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and its two specified projections.
- The additional canonical structures come from `Mathlib.AlgebraicGeometry.Group.Affine`
  (`instGrpObjSpecAsOverSpec` and its multiplication/unit formulas),
  `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`, and
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod` (`CategoryTheory.ModObj`).

All already-stated proof-dependency modules are imported explicitly, including
`Sheaf.AlgebraicGeometry.FineFanBlowup`,
`Mathlib.LinearAlgebra.FreeModule.PID` (`Module.basisOfFiniteTypeTorsionFree'`),
`Sheaf.RingTheory.AffineMonoidAlgebraNormalization`
(`MonoidAlgebra.affine_monoid_algebra_normalization`),
`Sheaf.RingTheory.GeometricallyReducedBaseChange`
(`isReduced_tensorProduct_of_forall_fieldExtension`),
`Mathlib.AlgebraicGeometry.Scheme` (`Spec` and `Spec.map`),
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
(`LocallyOfFinitePresentation`), and
`WeilConjectures.AlgebraicGeometry.Thickening` (`IsFirstOrderThickening`). The last
was read with `scompile.py --source WeilConjectures.AlgebraicGeometry.Thickening`
because it is absent from the older slopmaster2 source checkout. The theorem's
docstring contains all ten proof steps and names their DAG inputs. Legacy imports
follow the recorded monoscheme module, whose FineFan dependency is a legacy file.

Edge cases checked against the definitions and the source proof:

- Empty monoscheme: no `ToricComponent` exists, and the realization is the empty
  gluing. Reducedness and finite type hold; there are zero connected components.
- Rank zero: the exponent group `Fin 0 → ℤ` is trivial, its group algebra is the
  coefficient field, and the coordinate torus is Spec Q with its trivial group.
- Nontrivial monoid units and nonsaturated monoids: no sharpness, saturation,
  separatedness, or normality hypothesis has been added. The realization need only
  be reduced and componentwise integral; a nonnormal cusp-type monoid is included.
- Empty Y: its product is empty, and the map to empty Y is smooth and surjective.
- Reducible reduced Y: reduced tensor-product input applies without an integral Y
  assumption. The statement does not force Y to be connected or nonempty.
- Empty finite union: n=0 is allowed, with the initial scheme and canonical initial
  structure morphism. Arbitrarily many (finite) summands and rank-zero tori remain.
- General universe: the theorem compiled with explicit u and the lifted rational
  field, without an extra universe equality or auto-bound variable.

Searches performed in this attempt (all through the prescribed tools or read-only rg):

1. `msearch.py ... leanfinder "fine torsion free monoscheme toric realization reduced
   finite type split torus action smooth projection"`: OK, eight hits concerning Proj,
   affine space, smooth relative dimension, and related general scheme notions; no
   whole-statement match.
2. `msearch.py ... loogle '"MonoidAlgebra", "IsDomain"'`: OK, two hits,
   `AddMonoidAlgebra.instIsDomainOfIsCancelAddOfUniqueSums` and
   `MonoidAlgebra.instIsDomainOfIsCancelAddOfUniqueProds`; only affine algebra
   fragments, not this gluing/component/group-action statement.
3. `msearch.py ... grep 'toric|splitTorus|Toric' AlgebraicGeometry`: OK, zero hits.
4. Read-only rg in upstream `WeilConjectures`, current `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for the item id and `toric_realization_finite_type`:
   no existing statement. Searching `toric.*finite`, `splitTorus`, `SplitTorus`, and
   `torus.*[Mm]ul` found no existing replacement for the whole theorem.
5. Read-only rg for `torusGroup|coordinateTorusGroup` in Mathlib, upstream
   `WeilConjectures`, and current `lean/Sheaf`: no declaration-name collision.
6. Read Mathlib's Grp, ModObj, affine-group, monoid-algebra Hopf and coalgebra
   declarations. These provide the genuine canonical group and action interfaces,
   so no private copies or new independent notion are needed.

There is no `STATEMENT-DISPUTED` issue or natural-language node correction. The
node copy changes only `lean`. All data in both helper abbreviations are real;
the sole postponed theorem is the item's named theorem.

## Second reading by NO

This is a second pass by the dispatched worker, not an independent agent review:
the dispatch explicitly forbids starting other agents. The maintainer's independent
review remains the delivery review described in the brief.

With both node and file open, I matched each row above against the final signature.
The earlier sandbox had a scheme-only isomorphism and a first-projection smoothness
claim; these failed the group-isomorphism and projection-to-Y clauses. The repaired
file uses a `Grp` isomorphism with the canonical Hopf group structures, a genuine
`ModObj` action identified with the specified coaction map, and `pullback.snd` for
the projection to Y. Product finite type is stated on its composite map to Q.
The old universe-zero binders became arbitrary u using the lifted rational field.
I also checked that integral component opens exhaust the actual ambient connected
components via the explicit range equality; the earlier file did not express this
identification. Finite sums now use the canonical `Sigma.desc` structure morphism.
No extra sharpness, normality, nonemptiness, characteristic, or separatedness
assumption was introduced. The empty, nonsaturated, rank-zero, reducible-base, and
finite-empty-union cases above are all retained.

The main theorem's proof is exactly `by sorry`; both helpers simply bundle actual
canonical structures. The module compiled cleanly through `scompile.py` before
packaging (4.0 seconds sandbox and 4.2 seconds module, with no errors or warnings).
The delivery dry run below verifies the final import list and record as well.
