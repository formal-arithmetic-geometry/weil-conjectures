## Worker report

The module `Sheaf.CategoryTheory.Localization.OrdinaryCommaRetractionNaturality`
states `CategoryTheory.OrdinaryCommaRetraction.exists_strict_naturality`. Its only
postponed theorem has proof `sorry`; its docstring gives all seven calculations
of the node. There are no hollow definitions or extra assumptions.

The source was read online: Dwyer–Kan, *Calculating simplicial localizations*,
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf,
Section 9.1 (printed p.31) gives the total category and its simultaneous base and
endpoint functoriality; 9.10 (printed p.32) supplies the comma retraction. The node
expands these into the displayed strict identities. I also read the current
blueprint proof `prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2.
Its derived coefficient-adjunction calculation is the recorded ancestry, not a
claim that the current blueprint prints the elementary comma formulas itself.

Hypotheses and constructions, matched with the Lean:

- Small ordinary bases are `C D E : Cat.{u,u}`; small values are
  `F : Cᵒᵖ ⥤ Cat.{v,v}`, `G : Dᵒᵖ ⥤ Cat.{v,v}`, and
  `Q : Eᵒᵖ ⥤ Cat.{v,v}`. The independent base/value universes cover the
  stipulated size enlargement; no nonemptiness or equivalence is imposed.
- The node's `A_F` is the abbreviation `Total C F = SSet.Thomason.Gr Cᵒᵖ F`.
  It reuses the project's recorded total category, itself the opposite of
  Mathlib's Grothendieck construction of the opposite fibers. The pair `(c,a)`
  is `op ⟨op c, op a⟩`. The base of an arrow is `f.unop.base.unop` and its fiber
  arrow is `f.unop.fiber.unop`, of type `a ⟶ F(h)a'`. The existing category
  structure has exactly the node's identity and composition, with only the
  equality transports required by strict functor laws.
- `projection C F` is the opposite of `Grothendieck.forget`, followed by the
  canonical `opOpEquivalence C` functor. It sends the preceding pair/arrow to
  `c`/`h`; it defines no second category structure.
- `CommaFiber C F c` abbreviates `StructuredArrow c (projection C F)`.
  Its object is precisely a total object `x.right` and arrow `x.hom : c ⟶ Px`;
  its morphism has total arrow `f.right` and triangle `x.hom ≫ P.map f.right = y.hom`.
  Composition and identities are the existing comma operations. Its action on
  `s : b ⟶ c` is the existing `StructuredArrow.map s`, sending `t` to `s ≫ t`
  and retaining `f.right`.
- The simultaneous existential families `R`, `K`, and `L` are quantified over
  every such diagram/change datum. They are functors, so identities and
  composition are included in their types. Their data are completely
  characterized by the following formulas; no arbitrary map is substituted.

The thirteen conjuncts of the theorem, in order, render every conclusion:

1. R objects: `(R C F c).obj x = (F.map x.hom.op).toFunctor.obj
   x.right.unop.fiber.unop`, exactly `F(t)a`.
2. R arrows: `HEq ((R C F c).map f)
   ((F.map x.hom.op).toFunctor.map f.right.unop.fiber.unop)`, exactly `F(t)u`.
   The comma triangle identifies its terminal object with `F(t')a'`.
3. K objects: equality with `op ⟨op (Hc), op (alpha_c a)⟩`.
4. K arrows: base `HEq` with `H.map f.unop.base.unop` and fiber `HEq` with
   `(α.app x.unop.base).toFunctor.map f.unop.fiber.unop`. Naturality supplies
   the necessary endpoint equality; no map beyond alpha and H is assumed.
5. Projection: `K ... ⋙ projection C F = projection D G ⋙ H`.
6. L objects: its right component equals `K.obj x.right`, and its structural
   arrow has `HEq` with `H.map x.hom`, exactly `(Kx,Ht)`.
7. L arrows: its right component has `HEq` with `K.map f.right`, exactly `Kv`.
8. Strict precomposition: `StructuredArrow.map s ⋙ L ... b =
   L ... c ⋙ StructuredArrow.map (H.map s)`.
9. Retraction square: `L ... c ⋙ R C F (H.obj c) =
   R D G c ⋙ (α.app (op c)).toFunctor`.
10. Strict K composition, for `J : E ⥤ D` and `γ : Q ⟶ J.op ⋙ G`:
    `K ... (J ⋙ H) (γ ≫ Functor.whiskerLeft J.op α) = K ... J γ ⋙ K ... H α`.
    The composite endpoint component is exactly gamma followed by alpha at Jc.
11. The identical strict composition law for L, with the intermediate L based
    at `J.obj c`.
12. K at `(𝟭 C,𝟙 F)` equals `𝟭 (Total C F)`.
13. L at `(𝟭 C,𝟙 F)` equals `𝟭 (CommaFiber C F c)`.

The component `HEq`s only express dependent-arrow equalities after identifying
source and target objects by the already prescribed formulas. The projection,
precomposition, square, composition and identity laws use ordinary `=` between
functors, never a natural isomorphism. Existentially quantifying the complete
families states their simultaneous construction and laws without defining data
by a mere unproved existence choice. A future proof constructs the functors.

Dependencies read and used:

- `Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus`,
  `CategoryTheory.RelativeZigzag.HasTwoSidedHomotopyCalculus` and
  `zigzagNerve`: the recorded small ordinary-category/ordinary-nerve convention.
  This theorem is the categorical precursor; it assumes no homotopy calculus.
- `Sheaf.AlgebraicTopology.ThomasonGrothendieckComparison`,
  `SSet.Thomason.Gr`: the already recorded total-category construction, whose
  full definition and docstring were read. Its owner node
  `lem-coef-thomason-grothendieck-comparison` is added to `stmt_deps` under the
  standing rule allowing an existing landed declaration's node to be cited.
  No field of that dependency node is changed. This dependency has no path
  back to this item (its dependencies are the BK comparison, weak-equivalence,
  bisimplicial diagonal, basepoint, nerve homotopy and cylinder nodes).
- Mathlib `Grothendieck.forget`, `Cat.opFunctor`, `opOpEquivalence`,
  `StructuredArrow`, `StructuredArrow.map`, and `Functor.whiskerLeft` provide
  projection, comma/precomposition and the composite transformation.
  The full relevant definitions were read in their source modules.

Edge cases checked before drafting and again on the final signature: an empty
base leaves no total or comma objects, and all formulas and laws remain valid;
empty individual fibers and absent homs remain empty with no chosen objects;
identity transformations and identity base functors have explicit laws; constant
terminal fibers specialize to ordinary comma categories; noninvertible base
arrows, nonfaithful or nonequivalence H, and arbitrary noninvertible alpha
components are admitted; arbitrary composable changes are quantified in the
same families. Both universes are explicitly bound and independent, and no
auto-implicit binder is used.

Searches:

- `msearch.py ... leanfinder "Strict naturality of the contravariant Grothendieck
  comma retraction under base functors and natural transformations"`: 8 hits,
  including `Grothendieck.ιNatTrans`, `ιCompMap`, `map_map`,
  `Pseudofunctor.CoGrothendieck.map_map_fiber`, and generic reindexing results.
  These do not state the simultaneous comma retraction square with its laws.
- `msearch.py ... loogle "CategoryTheory.Pseudofunctor.CoGrothendieck,
  CategoryTheory.StructuredArrow.map"`: 0 hits.
- `msearch.py ... grep "CoGrothendieck|comma.*[Rr]etract|[Rr]etract.*comma"
  CategoryTheory`: 10 hits, the generic CoGrothendieck and unrelated retract
  properties. The ordinary and pseudofunctor Grothendieck source files and
  comma basic/structured-arrow source were read. No exact theorem match.
- `rg` of `WeilConjectures` and `lean/Sheaf` for comma/retraction and
  CoGrothendieck terminology found no full theorem. A broader final check found
  `SSet.Thomason.Gr` and its use by `TwoSidedSimplicialGrothendieck.projection`.
  The final file uses Gr rather than introducing a different CoGrothendieck
  model. The latter module's projection is specialized to values in a larger
  `max` universe and belongs to a downstream proof; it is not imported to
  create a dependency cycle. Here projection is only an abbreviation for the
  existing Mathlib forget/op-op functors, valid for independent universes.
- `rg` for `OrdinaryCommaRetraction` and `exists_strict_naturality` in Mathlib,
  upstream project, current project and `dag/lean_names_upstream.json`: no
  name collisions. Searching the item id in upstream `WeilConjectures` found
  no existing attachment.

No statement correction, disputed statement, new node, or dependency repair
was needed. The original node fields are preserved except `lean` and the
additional landed-owner statement dependency described above.

Validation: the final file was compiled by `scompile.py N7
lem-coef-ordinary-comma-retraction-naturality` in both sandbox and module-path
passes, clean with no errors or warnings. No direct compiler or global build
was run.

## Second reading by N7

Final self-check by the dispatched worker; no additional agent was started.
The maintainer supplies the independent reading. I reopened the node and the
final file and checked all thirteen conjuncts against the clauses above.
Specifically, the opposite-base/opposite-fiber encoding retains the node's
forward base h and fiber a → F(h)b; R applies F(t) on arrows, not just objects;
K applies the source component of alpha; L retains the K-arrow; all strict
squares and both identity/composition laws are ordinary equalities. The one
interface adjustment was switching the draft's direct CoGrothendieck alias to
the existing `SSet.Thomason.Gr`, and adding its existing owner dependency.
The arrow formulas require HEq because the adjacent object equalities are
propositional, which does not weaken their characterization. There are no
extra equivalence/nonemptiness assumptions. Only the main theorem is sorry;
all three abbreviations expand to existing constructed data.
