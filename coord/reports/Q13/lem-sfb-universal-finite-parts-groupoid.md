## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.UniversalFinitePartsGroupoid`.
Declaration: `AlgebraicGeometry.universal_finite_parts_groupoid`.
This is one theorem with exactly `sorry` as its proof. There are no new definitions,
new nodes, dependency repairs, or statement corrections. Only the item's `lean`
field changes. The docstring contains all eight proof steps of the accepted node.

Source read: `literature/stacks-project/spaces-more-groupoids.tex`, Section
`section-finite-set-arrows`, Section `section-finite-part-groupoid`, Tag 04RU
(`lemma-finite-part-groupoid`), and Tag 04PH (`lemma-finite-separated`). Also read the
current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/_section.md`. This is the supporting groupoid construction,
not a change to the unit's six-functor assertion.

Hypotheses and clauses, matched individually:

| Node | Lean |
| --- | --- |
| A scheme S and S-schemes U,R | `{S : Scheme.{u}}`, `U R : Over S` |
| Groupoid scheme over S | `s t : R ⟶ U`, `e : U ⟶ R`, `i : R ⟶ R`, `c : pullback s.left t.left ⟶ R.left`, `hG : IsGroupoidScheme ...` |
| Composition also over S | Follows from `hG.composition_source` and `s` being an Over morphism; no extra hypothesis needed |
| s,t separated | `[IsSeparated s.left] [IsSeparated t.left]` |
| s,t locally of finite type | `[LocallyOfFiniteType s.left] [LocallyOfFiniteType t.left]` |
| M is an S-scheme | `M : Over S` |
| g is the forgetful etale S-morphism | `g : M ⟶ U`, `[Etale g.left]`, `hforget` |
| M represents precisely the finite-open-pair functor | `E : ∀ T : Over S, (T ⟶ M) ≃ (Σ a : T ⟶ U, {Z : ... // ...})`, with `huniv` |
| a is a map T→U over S | Sigma entry `a : T ⟶ U` |
| Z is an open subscheme of the source fibre | `Z : (pullback s.left a.left).Opens` |
| Z finite over T | `IsFinite (Z.ι ≫ pullback.snd s.left a.left)` |
| Z contains the entire unit section | The actual lift `v : T.left ⟶ Z.toScheme`, with arrow projection `a.left ≫ e.left` and base projection `𝟙 T.left` |
| Q is the universal open | `Q : (pullback s.left g.left).Opens`; `huniv` identifies every classified Z with `b ⁻¹ᵁ Q`, and specifies both projections of b |
| Point of Q is a triple (a,Z,z) with sz=a and z in Z | A map `q : T.left ⟶ Q.toScheme` has arrow coordinate `q ≫ Q.ι ≫ pullback.fst ...` and object coordinate through the second projection; `E` and `huniv` identify its pair, with factorization through the actual open subscheme |
| Source is (a,Z) | `sQ = Q.ι ≫ pullback.snd s.left g.left` |
| Target has first coordinate tz | The target compatibility equation `(Q.ι ≫ pullback.fst ...) ≫ t.left = tQ ≫ g.left` |
| Target finite part is c(Z,iz) | The final universally quantified clause gives `τ` between the two source fibres, with `τ.hom` the specified right translation and `(E T n).2.val = τ.inv ⁻¹ᵁ (E T m).2.val` |
| Translation is an isomorphism with inverse r↦c(r,z) | `τ : ... ≅ ...`; `k` and `l` have both projections fixed, and `τ.hom ≫ fst = k ≫ c`, `τ.inv ≫ fst = l ≫ c` |
| Translation respects the test base | `τ.hom ≫ snd = snd`; the inverse respects it by the iso identities |
| Unit triple (a,Z,ea) | The groupoid unit laws force source and target to be the same object; `eQ ≫ Q.ι ≫ fst = g.left ≫ e.left` fixes the arrow coordinate |
| Inverse triple (tz,c(Z,iz),iz) | The groupoid inverse laws swap its endpoints and `iQ ≫ Q.ι ≫ fst = (Q.ι ≫ fst) ≫ i.left` fixes the arrow coordinate |
| Composition triple (a2,Z2,c(z1,z2)) | The groupoid composition source law fixes the second object's pair; the universal equation with test maps `p,d` fixes the arrow coordinate to `d ≫ c` |
| All formulas are morphisms, not just point rules | Existentially bound `sQ,tQ,eQ,iQ,cQ` are scheme morphisms |
| All groupoid axioms | `IsGroupoidScheme sQ tQ eQ iQ cQ`, using the recorded dependency |
| Structure over S | `tQ ≫ M.hom = sQ ≫ M.hom`; source has the prescribed structural map, and the unit, inverse and composition laws imply that the other maps are over S |
| Morphism of groupoids with object map g and universal arrow projection | The five compatibility clauses for source, target, identity, inverse and composition; arrow map is exactly `Q.ι ≫ pullback.fst ...` |
| Both source and target finite | `IsFinite sQ ∧ IsFinite tQ` |
| Q open and closed | `Q` is an Opens value and `IsClosed (Q : Set ↥(pullback s.left g.left))` |
| No affineness or quasi-finiteness assumption | No such binders occur |

Why the representation hypothesis is exact: the projection equations uniquely fix b.
The open equality in `huniv` therefore forces E to classify pullbacks of the supplied
universal Q. This already implies naturality under arbitrary S-scheme maps: inverse
images compose and the two projection equations determine the composite comparison.
Conversely any representation with its universal open gives these E, hforget and
huniv. Thus no arbitrary bijections or arbitrary finite families have been substituted.
For the final translation clause, every S-test arrow q has unique S-maps m,n obtained
from its source and target. Its quantifiers are consequently nonvacuous. The maps k,l
are canonical maps into fibre products, fixed by BOTH projections, not extra choices.
The composition clause similarly quantifies over the uniquely determined induced map d;
its existence follows from the endpoint compatibility clauses.

Dependency declarations used, with their modules:

- `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Scheme.Opens`:
  `Mathlib.AlgebraicGeometry.Scheme` (def-pc-scheme).
- `AlgebraicGeometry.IsGroupoidScheme`:
  `Sheaf.AlgebraicGeometry.GroupoidScheme` (def-a1-groupoid-scheme).
  Its full signature and all fields were read. The composition convention is a∘b,
  with s(a)=t(b), matching the source and this module.
- `AlgebraicGeometry.IsSeparated`, `IsProper`:
  `Mathlib.AlgebraicGeometry.Morphisms.Separated` and `.Proper`
  (def-weil-proper-morphism).
- `AlgebraicGeometry.LocallyOfFiniteType`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  (def-weil-finite-type-morphism; the quasi-compact part is not assumed here).
- `CategoryTheory.Limits.pullback`, `.fst`, `.snd`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
  (def-pc-fibre-product).
- `AlgebraicGeometry.IsOpenImmersion` and `Scheme.Opens.ι`:
  `Mathlib.AlgebraicGeometry.OpenImmersion` (def-weil-open-immersion).
- `AlgebraicGeometry.IsFinite`:
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`
  (def-weil-finite-integral-morphism; integrality is not separately assumed).
- `AlgebraicGeometry.Etale`:
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (def-weil-etale-morphism).

The proof-dependency interfaces are imported: `Mathlib.CategoryTheory.Yoneda`
plainly, and the open-immersion/base-change, finite-permanence, separated-base-change,
finite-proper and `IsProper.of_comp` APIs through the public Mathlib modules already
needed by the signature. There is no proof-only Sheaf module missing from the imports.

Edge cases checked:

- Empty S, empty U, or empty M: no Nonempty assumption; empty test schemes remain
  permitted. An empty finite part over a nonempty T is excluded only by the required
  unit lift, exactly as in the source. Over empty T that lift exists.
- Trivial groupoid: the only marked finite part is the full unit source fibre;
  translation and the resulting groupoid are identities.
- A constant C3 group: a finite part {1,h} is permitted without being a subgroup;
  translation by h sends it to {h⁻¹,1}, and the target open formula has that direction.
  This also checks the direction `τ.inv ⁻¹ᵁ Z`, which is the image of Z under τ.
- Positive-dimensional source fibres (for example G_m over a field): the parameter
  scheme may be empty; no finite part is presumed to exist over a nonempty test.
- Nonreduced test schemes: the unit is an actual scheme section, and translation is
  an isomorphism of full fibre schemes. Membership is not checked only on geometric
  points. All structures and all tests use the same arbitrary universe u, as in the
  scheme-groupoid dependency, without a size restriction or unrelated test universe.

Searches, all made through the prescribed wrapper and read-only source searches:

- LeanFinder, `Internal groupoid of universal finite open source parts containing
  the identity with right translation`: 8 hits, manifold StructureGroupoid and its
  identity/restriction variants; none concerns internal groupoids in schemes.
- Loogle, `"Groupoid", "finite"`: 0 hits.
- Mathlib grep, `Groupoid|finitePart|finite_part`, subdirectory AlgebraicGeometry:
  0 hits.
- LeanSearch, `Universal finite open source parts of a groupoid scheme with
  translation form a groupoid`: 8 hits, StructureGroupoid and abstract category
  Groupoid/SmallGroupoid, no matching internal construction.
- `rg` for `finite.part|FinitePart|finitePart|finite_part|UniversalFinite` in the
  project and upstream AlgebraicGeometry sources: unrelated finite-parts presentation,
  strata and trace modules, no groupoid construction.
- `rg` for the node id and `universal_finite_parts_groupoid` in all of
  `lean/WeilConjectures` and `lean/Sheaf`, plus `grep -rn` for the node id upstream:
  only the proof-plan mention in AffineGroupoidPointedQuasisplitting, no declaration.
- `rg` in `dag/lean_names_upstream.json`: no matching declaration.
  The existing `GroupoidScheme` API was read and reused; the pair sigma encoding is
  consistent with `UnmarkedFiniteOpenPartsSpace`, whose declaration was also read.

Validation: prescribed `scompile.py`, all files compiled individually, server clean
in 2.9 seconds (60-second limit, nice 19, two threads). The local compiler attempt
reported `OSError(28, 'No space left on device')`; the wrapper automatically confirmed
against the server successfully. The first server compile caught a Set coercion
ambiguity in the closedness clause; corrected to explicit `Set ↥(...)` and recompiled.
No unexpected warning remains. No STATEMENT-DISPUTED or node fault.

## Second reading by Q13

Author's separate clause-by-clause self-check, not an independent reviewer: opened
both the accepted JSON statement and the completed Lean signature. Independent review
is the maintainer's delivery review, as specified in this dispatch brief; no sub-agent
was started. Checked especially that the test-scheme class is Over S, the open contains
an actual unit section, the supplied universal Q determines the representing bijections,
all structure maps are over S, and both projection equations specify every auxiliary
fibre-product map. The source/target order and the inverse-image direction for translation
agree with Stacks. The identity and inverse triple formulas follow from the endpoint
laws plus their explicit arrow-coordinate equations; composition includes the actual
induced map on composable pairs. Only the explicit scheme-carrier coercion needed a
compiler repair. No mathematical mismatch was found and the node statement is unchanged.
