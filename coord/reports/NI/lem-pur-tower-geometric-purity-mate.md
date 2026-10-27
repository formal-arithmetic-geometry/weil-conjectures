## Worker report

The module `Sheaf.Paper.TowerGeometricPurityMate` states
`WeilConjectures.PurityFiniteSetting.tower_geometric_purity_mate`, with exactly one
postponed theorem. Its proof is `sorry`, with the five-step DAG proof in the docstring.
All other declarations construct or package the maps in this very statement. There
are no new coefficient categories, tensor products, orientations, or adjunctions.

Hypothesis-by-hypothesis and clause-by-clause reading:

- The datum `(S : PurityFiniteSetting.{u})` supplies the fixed finite field, its
  algebraic closure, prime ell different from its characteristic, finite coefficient
  extension, valuation ring and uniformizer. Its finite-level index is unused by the
  tower conclusion; the coefficient extension and every ell-power quotient are used.
- `X₀ Y₀ : Over (Spec (.of S.field.k₀))`, with `LocallyOfFiniteType`, `QuasiCompact`
  and `IsSeparated` on each structural map, render separated finite-type models.
  The same three binders on `f₀.left` render the separated finite-type model map.
- The base changes are precisely the recorded `S.frobeniusFiber` and
  `S.frobeniusMap f₀`. The binder `d : ℕ` includes zero;
  `[SmoothOfRelativeDimension d (S.frobeniusMap f₀)]` is pure smooth relative dimension.
  `c : Compactification ...` is the chosen compactification allowed in the source.
  No properness of f, connectedness or nonempty-scheme assumption is introduced.
- `S.frobeniusGaloisMap X₀` and `... Y₀` are the prescribed geometric-Galois actions,
  id times Spec(gamma). The output `sq` is their actual Cartesian square. The equation
  `c.comm` only replaces f by its open/proper factorization; no model morphism changes.
- `TowerGeometricPurityConclusion` installs Noetherian instances from the finite-type
  structural maps, and compactifiability from the displayed factorization. These are
  consequences, not new mathematical hypotheses. Its local instance bindings are
  inside the fully written definition, not hidden let-bound objects in a theorem.
- The universally quantified `b,o,x,q,z,h,cal` are the existing normalized operation,
  evaluation and compactification-calculus presentations. `SpTowerShriek.Laws` fixes
  the proper/open exchange and all quotient transitions. The `Preservation` and
  `Calculus` parameters express the existing restriction of those operations to ctf
  towers, and are used only to obtain the recorded canonical refinement comparison.
  They are not arbitrary maps between functors. This is the same supplied-operation
  interface used by tower gluing and tower exceptional base change.
- `SpTowerCalculus.C` is the full uniform bounded-constructible finite-Tor subcategory
  of the ordinary strict varying-coefficient tower derived category. Each natural
  index n means the positive quotient exponent n+1, so the first quotient is retained.
  `a : SpTowerGamma.Purity ...` is the *specified* purity data, including normalized
  finite diagonal orientation and actual orientation/tensor-mate factorization.
  Its maps are reused by `purityIso`; an arbitrary natural isomorphism is not accepted.
- `Result.pullX` and `pullY` supply ctf closure for Q and P. `Q` and `P` are actual
  `ObjectProperty.lift` restrictions of the recorded exact tower pullbacks.
  Every K in the identities ranges over this full category. No normalization is
  required of K in any purity identity, transpose assertion or root construction.
- `exchange` is `SpTowerMate.exchange` (proper/open base change for the actual square
  and pulled-back compactification), followed by
  `cal.composition.refinement f (c.ofIsPullback sq) c`. It is a natural transformation
  by construction. Thus the comparison is the canonical B on underlying sites after
  retagging, with the canonical same-compactification identification, not an arbitrary
  endpoint isomorphism. `Result.exchange_iso` states its invertibility on the full ctf
  category. The construction works for any chosen c, as required by the node.
- `mate` is Mathlib `mateEquiv adj adj` applied to inverse exchange. `Result.transpose`
  says explicitly that its component is `adj.homEquiv` of inverse B at GK followed by
  P applied to epsilon. This is exactly the displayed counit mate, not just some
  isomorphism of its source and target. `Result.mate_iso` states invertibility of this
  natural transformation, hence natural isomorphy of e.
- `Roots.line` is a map of ordinary strict systems before localization. Its
  `normalized` field fixes its ordinary adjunct on *all* finite scalar/root sections
  to the actual coefficient restriction and `SpTowerClasses.restrictRoot` on the
  pulled-back chart. `RootLines.normalized` fixes the comparison to the inverse-limit
  root projections. Thus the roots-of-unity tower map, its power transitions and
  coefficient quotient transitions are retained. No equality of derived morphisms
  is inferred from equality of their evaluations.
- `orderedRoots` starts at the constant-section-normalized coefficient unit, pulls
  the strict degree-one root line through its shift by two, and takes ordered tensor
  powers through the existing tensor-pullback comparison. This is tau_d on
  A_X(d)[2d], with no choice of scalar; at d=0 it is the coefficient unit map.
- `sourceComparison` is the existing tensor-pullback map followed by the inverse
  pullback-composition square, the equivalence-counit cancellation, and `orderedRoots`.
  It defines b independently of Gamma. `Result.source_naturality` records its
  naturality; every component is an actual isomorphism by its definition.
- `Result.retagging` expands to `Retagging`, quantifying a second exceptional-adjoint
  presentation on the same ordinary sites and compactification. It compares the
  whole orientation by `adjγ.rightAdjointUniq adj`, and compares both the actual
  inverse-projection/counit composite and its `tensorMate`. The comparison of right
  adjoints is the unique counit-preserving one. Retagging changes only the field
  structure maps; the underlying sites, c, operations and Tate towers in these
  formulas are literally shared. This is why no arbitrary retagging map is a binder.
- `Result.support_normalized` says PF and FQ preserve normalized inputs. Its
  `exceptional_normalized` says the same for QG and GP. Normalization is the recorded
  `IsSpNormalizedTower`, testing every canonical derived reduction, including m=n.
  Since B and e are isomorphisms between these full-subcategory objects, these are
  exactly their restrictions to normalized towers.
- `Result.purity_square` is `Q(Gamma_K) ≫ e_K = b_K ≫ Gamma_(PK)`;
  `Result.conjugation` is `e_K = (Q Gamma_K)⁻¹ ≫ b_K ≫ Gamma_(PK)`.
  Lean writes composition in traversal order. `pullRealization.inv` conjugates e
  into the same section-preserving coordinates as tower Gamma; it is the specified
  equivalence counit, not an extra comparison. The equalities are Hom equalities in
  `SpTowerShriek.D`, the ordinary derived category of strict systems, equivalent to
  `spDerivedCoefficientTowers` via the recorded section-preserving realization.

Dependency declarations read and reused:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated`, `IsProper`;
  the standard `QuasiCompact` class supplies the other finite-type condition.
- `Sheaf.SixFunctors.SchemeGeometricFrobenius`: `frobeniusFiber`, `frobeniusMap`,
  `frobeniusGaloisMap` in namespace `WeilConjectures.PurityFiniteSetting`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`;
  `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spConstructibleTorTowers`,
  `IsSpNormalizedTower`, `spNormalizedConstructibleTorTowerCategory`.
- `Sheaf.Paper.SmoothPurityTowerGluing`: `SpTowerGluing.support`, `Levels` and
  the fixed Mathlib adjunction. `Sheaf.Paper.SmoothPurityTowerGamma` reexports
  `SpTowerGamma.Purity`, `gamma`, `projectionCounit`, `tensorMate`, `orderedLine`,
  `source`, `realization`, and `factorization` from its new definition owner
  `Sheaf.Paper.SmoothPurityTowerGammaData`.
- `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` reexports
  `SpTowerMate.exchange` and its ordinary original-tower coordinate construction.
- `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`: the root-tower comparison
  `WeilConjectures.FrobeniusCoefficientTwists.rootTowerMap` and its root normalization
  are the specified twist convention. The formula here uses the existing equivalent
  strict finite scalar/root-section description, not completed tensor products.
- Added landed definition owners `def-sp-coefficient-tower-shriek-interfaces`,
  `def-sp-coordinate-right-comparisons`, `def-sp-tower-class-diagonal`,
  `def-sp-tower-class-pullback`, `def-sp-tower-gamma-data`,
  `def-sp-chart-tate-tower-data` give, respectively, `Calculus` and its canonical
  `composition.refinement`; `SpCoordinateAdjunction.RootLines`;
  `SpTowerClasses.CoefficientPullback` and `.derivedIso`; `adjointSection`,
  `chart`, `restrictRoot`; the existing `Purity` data; and `SpChartAdmissibility.Twists`.
  Their recorded modules are all imported publicly. No definition was duplicated.
- The local fiber structural-map instances use Mathlib's base-change instances for
  `pullback.snd X₀.hom β` and `pullback.snd Y₀.hom β`, where β is the scalar-extension
  map. `Over.pullback.obj` has exactly that structural map. The relative instances
  use `MorphismProperty.overPullbackMap` for `IsSeparated`, `LocallyOfFiniteType`
  and `QuasiCompact`, applied to `f₀.left`'s given instances. No finite-purity
  theorem module or its helper instances is imported or cited.
- Proof imports: Frobenius square (reexported), operations ground-field retagging
  (reexported), orientation ground-field retagging, tensor-transpose ground-field
  retagging, tower gamma, tower exceptional base change, tower gluing and inverse
  image along an isomorphism. `det-sp-purity-bc-factors` currently has no recorded
  Lean module; its proof import is omitted, as an unstated proof dependency, and
  its whole-tower assertions (1)--(2) remain the documented stage-3 input.

Searches made (the msearch wrapper records their exact output):

- LeanFinder: “Smooth purity commutes with geometric Frobenius pullback and the
  exceptional counit mate in the derived category of coefficient towers”: eight
  hits, ordinary scheme-module pullback composition and adjunction equations;
  none states strict-tower semilinear purity compatibility.
- Loogle: `"TateTwist"`: no hits.
- Mathlib grep: `purity|TateTwist|exceptionalBaseChange`: no hits.
- LeanSearch: “Smooth purity is compatible with geometric Frobenius on strict
  coefficient towers”: eight hits, perfection coefficients, smooth scheme class
  and field Frobenius; no match.
- rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  this node id and `geometric_purity_mate|geometricPurityMate`: only the existing
  finite-coefficient mate, which is not imported or used in the repaired delivery.
- Conceptual rg `semilinear.*purity|tower.*purity.*mate|purity.*tower.*mate` finds
  the rational theorem's docstring discussion of the required tower proof, not
  an existing statement of this theorem. Its actual definitions are rational/integral.

Edge cases checked before stating: d=0 uses the genuine coefficient unit; n=0
means quotient exponent one; equal reduction indices are retained by the existing
normalization predicate; empty models and zero towers require no nonemptiness or
chosen root section; arbitrary ramification is handled by `Base`'s recorded ideal
cofinality; K is unnormalized throughout; all equalities are ordinary derived Hom
equalities and no level-evaluation faithfulness premise is used. The small site
keeps its original object universe u+1 and morphism universe u, with coefficient
size u+1, through the reused tower interfaces.

No statement correction, disputed statement, new DAG node or dependency repair is
needed. Only the item's lean record and the authorized additions of landed notion
owners to stmt_deps are changed.

## Second reading by NI

The dispatcher explicitly forbids starting another agent. This section records a
separate self-audit, not a claim of an independent worker review; the maintainer's
independent review remains required. I reread the node beside the complete file.
The potential mismatch was that bare base change lands at a pulled-back
compactification, whereas the node fixes the same support functor. `exchange`
includes the existing canonical refinement back to that functor. Its naturality
is the composition of the two recorded natural transformations. I also checked
that b is root-normalized independently of purity, including d=0, and that the
mate uses inverse B in the correct direction. The output stores both whole-tower
equalities, actual transpose, orientation and tensor retagging, invertibility,
naturality, and both normalized-output pairs. No hypothesis normalizes K. The
finite auxiliary module and its stmt_dep have been removed in the H2 repair.
All remaining added stmt_deps have landed Lean records; the item statement and
proof are unchanged.

## Returned delivery repair: H2

The immutable returned head was cb74cd8a8147. The current read clone and the
server source query contain no landed `Sheaf.Paper.TowerGeometricPurityMate`
module; this repair continues the retained sandbox version. The delivery wrapper
rebases the packet on current main.

H2 is repaired by removing `lem-pur-finite-geometric-purity-mate` from `stmt_deps`
and removing its `public import`. In `TowerGeometricPurityConclusion`, six local
instances obtain locally finite type, quasi-compactness and separatedness of the
two fiber structural maps directly from Mathlib's `pullback.snd` base-change
instances. Explicit local aliases expose these same proofs for the canonical
`Scheme.Over` structure-map notation; this notation is a typeclass-search key that
does not automatically match the bundled `.hom` key. Three further local instances
use `MorphismProperty.overPullbackMap`
for these properties of the model map's actual scalar extension. This Mathlib
lemma applies pullback stability to the Cartesian square of `Over.pullback.map`.
Thus the subsequent `QuasiCompact (c.i ≫ c.g)` instance still comes from the actual
base-changed map by `c.comm`, with no dependency on sorried finite-purity helpers.
The Noetherian and structural-map instances needed by the conclusion remain
consequences of the original model hypotheses. The theorem signature and every
mathematical clause of `Result` are unchanged. No definition node is needed for
these existing Mathlib properties.

Repair search: read `Mathlib.CategoryTheory.MorphismProperty.Limits`, especially
`overPullbackMap`, `pullback_snd` and `of_isPullback`; read the pullback-snd instances
in Mathlib's `FiniteType`, `QuasiCompact` and `Separated` modules, and the exact
`frobeniusFiber`/`frobeniusMap` abbreviations in `SchemeGeometricFrobenius`.

Repaired-file validation: `scompile.py NI lem-pur-tower-geometric-purity-mate`
compiled the complete module in sandbox mode (57.2 s) and library mode (38.9 s),
with no errors or unexpected warnings. In particular the unchanged
`letI : QuasiCompact (c.i ≫ c.g) := c.comm ▸ inferInstance` elaborates using
the new Mathlib-backed local instance. The recorded theorem signature still
matches the module verbatim, with only one postponed theorem.
