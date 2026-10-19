## Worker report

`lean/Sheaf/AlgebraicGeometry/HigherDirectImagesLimits.lean` states
`AlgebraicGeometry.higherDirectImage_baseChange_of_limit`, with its only proof
`sorry`. Its source is [Stacks Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT),
second assertion, restricted to the torsion coefficients specified by the node.
The proof follows the two varying-base continuity comparisons in
[Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM), including the canonical-map
compatibility expanded in the node's five proof steps.

The earlier sandbox attempt compiled but did not state the node: its `D` was
indexed by `Iᵒᵖ`, and objectwise isomorphisms `hFi` imposed no relation between its
arrows and transitions of the stage sheaves. This delivery repairs both issues.
It also replaces the earlier abbreviated proof docstring with all five steps,
adds the recorded proof imports, and removes the earlier purported second
reading. The independent second reader has not yet read this revision.

Every clause of the node has the following rendering:

- A directed index set: `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. A preorder is the directed-set convention
  prescribed in the standing brief (Stacks 00D3). The index lives in the schemes'
  universe, as required by the project's size convention.
- Four inverse systems of schemes: `DX DY DS DT : Iᵒᵖ ⥤ Scheme.{u}`.
  Their functor laws are the identity and composition laws of scheme transitions.
- The arrows of the inverse system of squares: natural transformations `ηf`,
  `ηe`, `ηg`, `ηh`. Their naturality is exactly compatibility of these four
  families with the transition maps.
- Every stage square is Cartesian: `sqi i : ChosenCartesianSquare
  (ηe.app i) (ηh.app i) (ηg.app i) (ηf.app i)`. With this ordering, the upper-left
  scheme in `ChosenCartesianSquare` is `Y_i`, and its projections are `e_i` to
  `T_i` and `h_i` to `X_i`.
- Affine transitions in all four systems: the four families of
  `IsAffineHom (DX.map a)`, `IsAffineHom (DY.map a)`,
  `IsAffineHom (DS.map a)`, and `IsAffineHom (DT.map a)`.
- Each `g_i` is quasi-compact and quasi-separated: the instance families
  `QuasiCompact (ηg.app i)` and `QuasiSeparated (ηg.app i)`.
- The four limits: cones `cX`, `cY`, `cS`, `cT`, with their corresponding
  `IsLimit` witnesses `hcX`, `hcY`, `hcS`, `hcT`. The limit morphisms are `f`,
  `e`, `g`, `h`; `hf`, `he`, `hg`, `hh` say that their projections are those of
  the four natural transformations, hence these are the induced maps.
- The resulting Cartesian limit square: `sq : ChosenCartesianSquare e h g f`.
  This records the Cartesian identification that the node states the induced
  limit square has. No relation between transition stages being Cartesian is
  assumed. The choice of the identification does not enter the exchange map:
  that map uses only `sq.toCommSq`.
- The projections `p_i` are `cT.π.app i`.
- Abelian sheaves on the small étale sites: `Fi i : Sheaf
  (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}`. The `u+1` coefficient
  size is the recorded abelian-sheaf convention for `Scheme.{u}`.
- Torsion coefficients: `torsionFi i : CategoryTheory.Sheaf.IsTorsion (Fi i)`.
  This is local finite additive order of sections on a covering sieve; no
  uniform annihilator or torsion condition on every entire section group is
  substituted.
- The compatible sheaf system: for `a : i ⟶ j` in the forward category `I`,
  `φ a : (Etale.upperStar _ (DT.map a.op)).obj (Fi (op i)) ⟶ Fi (op j)`.
  Thus `DT.map a.op` is precisely `T_j → T_i`. `hφid` identifies the identity
  transition with canonical pullback along the identity (transporting
  `DT.map_id`); `hφcomp` identifies the composite transition with pullback of
  `φ a` followed by `φ b`, using the canonical `Etale.upperStarComp` and
  `DT.map_comp`. These are the two laws the node explicitly requires.
- The filtered diagram of pullbacks on the limit: `D : I ⥤ Sheaf
  cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1}`. The isomorphisms `ιF i`
  identify `D.obj i` with `p_i⁻¹F_i`. For each forward arrow `a : i ⟶ j`, `hD`
  requires its map, under these isomorphisms, to be the composite of the
  canonical comparison `p_i⁻¹ → p_j⁻¹a_ji⁻¹` and `p_j⁻¹(φ a)`. The comparison
  is the recorded `Etale.upperStarComp` with equality `(cT.w a.op).symm`.
  Consequently neither the arrows nor the colimit are arbitrary. Allowing
  isomorphic representatives `D.obj i` only expresses the same diagram with
  chosen identifications; the canonical diagram itself is an allowed choice.
- `F = colim_i p_i⁻¹F_i`: `cF : Cocone D`, `hcF : IsColimit cF`; `F` is
  `cF.pt`, with its specified colimit legs `cF.ι.app i`.
- A fixed `q ≥ 0`: `q : ℕ`, mapped to the integer cohomological degree `(q : ℤ)`.
- Every stage base-change map is an isomorphism: `hbase`, applying degree-`q`
  homology to `Etale.derivedBaseChangeMapPlus _ (sqi i).toCommSq` at
  `(DerivedCategory.Plus.singleFunctor _ 0).obj (Fi i)`.
- The limit base-change map is an isomorphism: the conclusion makes the same
  `IsIso` assertion for `sq.toCommSq` and the sheaf `cF.pt` placed in degree zero.
  The homology map has source `H^q(f⁻¹ Rg_* F[0])` and target
  `H^q(Rh_* e⁻¹ F[0])`. Exactness of inverse image identifies these with
  `f⁻¹R^qg_*F` and `R^qh_*e⁻¹F`. Those canonical identifications are
  isomorphisms, so this is precisely the node's degreewise base-change
  assertion, as in the recorded `lem-kun-bc-map-on-cohomology` interface.

Dependency declarations read and used:

- `def-weil-pbc-cartesian-square`: `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`, including its chosen pullback
  isomorphism and both projection equations.
- `def-weil-pbc-scheme-conventions`: this is explicitly a convention record,
  with no declaration of its own. Its scheme and morphism notions are
  Mathlib's `Scheme`, `QuasiCompact`, and `QuasiSeparated`.
- `def-weil-pbc-etale-sheaves`: the recorded
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` imports the existing
  `CategoryTheory.Sheaf.IsTorsion` from
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
  Abelian sheaves are the recorded `Sheaf T.smallEtaleTopology AddCommGrpCat`.
- `def-weil-pbc-inverse-image`, `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction`, and derived `rightDerivedLowerStarPlus`.
  The same module supplies `upperStarComp`; its canonical identity comparison
  `upperStarId` is imported from `UpperLowerStar.Coherence`.
- `def-weil-pbc-derived-exchange`:
  `WeilConjectures.SixFunctors.BaseChange.Derived`,
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`. Its full signature gives
  `g^* Rf_* → Rf'_* g'^*`; at `(e,h,g,f)` this is the orientation required here.
- `def-weil-pbc-category-colimit`: Mathlib `CategoryTheory.Limits.Cocone`,
  `IsColimit` (in `Limits.Cones` and `Limits.IsLimit`, reexported through the
  recorded `Limits.HasLimits`). A colimit cocone is supplied rather than a
  second chosen-colimit construction.
- `pqf-def-affine-morphism` is a Mathlib leaf, using its `mathlib_match`:
  `AlgebraicGeometry.IsAffineHom`,
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`. It has no `lean` record and
  requires none.

Recorded proof dependency modules are imported without `public`:
`Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageColimits`,
`Sheaf.Paper.KunBcMapOnCohomology`, and
`Sheaf.AlgebraicGeometry.EtaleInverseImageExact`.
The Mathlib mate-pasting and exact-functor homology interfaces are imported
from `Mathlib.CategoryTheory.Adjunction.Mates` and
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
Quasi-compact and quasi-separated base-change permanence is supplied by the
already imported Mathlib morphism modules. `lem-kun-0eym` has no Lean record
on the shared DAG; it is a proof dependency only, needed for the eventual proof,
not for any object or map appearing in this statement. No missing statement
interface, new node, or dependency repair is needed.

Edge cases checked before the revision: the index is nonempty, so an empty
filtered system is excluded exactly as for directed sets; arbitrary preorder
indices are allowed without antisymmetry; a singleton index reduces to the
stage assertion; `q = 0` is included; the zero sheaf and the empty scheme are
allowed; no nonzero, finite coefficient, uniform torsion exponent, field-base,
or additional Cartesian condition on transitions is imposed. The stage
transition maps need not be isomorphisms. Identity and composite coefficient
transitions are explicitly constrained even when the scheme diagram is
constant. All variables and universes are explicitly bound, with
`set_option autoImplicit false` enabled.

Searches made in this revision (all on 2026-10-16):

- `msearch.py leanfinder`: query “An inverse system of cartesian squares of
  schemes with affine transition maps preserves higher direct image base
  change isomorphisms under inverse limits”. Eight results, including
  `AlgebraicGeometry.exists_app_map_eq_map_of_isLimit`,
  `exists_appTop_π_eq_of_isLimit`, `exists_map_preimage_eq_map_preimage`,
  and `Scheme.IsLocallyDirected.fst_inv_eq_snd_inv`. These concern functions
  or geometry on limits and gluing, not the stated étale base-change theorem.
- `msearch.py loogle`: query `"baseChange"`. Twelve tensor-product scalar
  extension results (`Submodule.baseChange`, `LinearMap.baseChange`,
  `LinearEquiv.baseChange` and their laws), with no match for this theorem.
- `msearch.py leansearch`: query “Higher direct images along inverse limits
  of cartesian squares with affine transition morphisms preserve base change
  isomorphisms”. Service unavailable: Internal Server Error. This result is
  recorded as unavailable, with no mathematical verdict inferred from it.
- `msearch.py grep`: `higherDirectImage|directImage.*filtered.*colimit`,
  both in `CategoryTheory` and across Mathlib: zero hits.
- `rg` in the source `WeilConjectures` and project `lean/Sheaf`:
  `higherDirectImage|IsTorsion|derivedBaseChangeMapPlus|Cocone D|hFi`,
  `0EZT|baseChange.*limit|higherDirectImage`, and
  `baseChange.*[Ll]imit|[Ll]imit.*baseChange|0EZT`.
  Existing generic derived-exchange maps and fixed-base continuity appeared;
  no varying-four-scheme limit base-change theorem was found. The same
  base-change/limit search was also run in all Mathlib sources.
- `rg "lem-kun-0ezt"` in the source library: no hit.
- Read the full signatures and docstrings of
  `Etale.higherDirectImage_limit` in
  `SmoothBaseChange/HigherDirectImage/Transition.lean` and
  `Etale.preservesColimitsOfShape_higherDirectImage` in `FilteredColimit.lean`.
  The former has a fixed target `S`, coefficients pulled back from one `W`,
  and a stalkwise conclusion; the latter fixes the morphism. Neither is the
  varying-system statement here, so neither can replace this declaration.

No `STATEMENT-DISPUTED` flag or node-statement fault. The only JSON field
changed against the shared node is `lean`; its signature is copied verbatim
from the Lean declaration. No proof has been supplied, no new definition
has been introduced, and no independent second reading is claimed here.

Validation: the revised coefficient interface compiled cleanly through
`scompile.py NO lem-kun-0ezt` (sandbox and library contexts). The final
`deliver2.py NO lem-kun-0ezt --no-push` dry run also compiles the delivered
file and runs the server preflight; its result is recorded by the tool.


## Second reading by NO

Independent second reading, 2026-10-16. I read the shared node, the sandbox
module, all eight statement-dependency records, and the declarations used from
those records. I also read the proof-dependency records to check the imports.
This reading concerns the revised module described in the Worker report; I did
not write that revision.

Source check: the Stacks checkout is absent on this machine. I fetched and read
the raw upstream `etale-cohomology.tex` in
`scratchpad/sources/etale-cohomology.tex`, including
`lemma-base-change-Rf-star-colim` (Tag 0EZT),
`definition-inverse-system-sheaves`, `lemma-relative-colimit-general` (0EYM),
and the opening of `section-base-change-preliminaries`.
I also checked [0EZT](https://stacks.math.columbia.edu/tag/0EZT) and
[0EYM](https://stacks.math.columbia.edu/tag/0EYM) on the Stacks website.
The surrounding source imposes no field, characteristic, Noetherian, properness,
or global quasi-compactness assumption. The node explicitly takes the torsion
case of the source's abelian-sheaf assertion; retaining that hypothesis is right.

The following is my complete list of objects, hypotheses, and conclusion clauses,
matched with this module's actual binders. Each verdict is against the node.

| Node item | Lean rendering and verdict |
| --- | --- |
| A directed set I | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`. Pass: the project's nonempty directed-preorder convention, with no antisymmetry restriction. |
| Four inverse systems X_i, Y_i, S_i, T_i | `DX DY DS DT : Iᵒᵖ ⥤ Scheme.{u}`. Pass: scheme transitions run from later stages to earlier ones. |
| Four arrows f_i, e_i, g_i, h_i compatible with transitions | `ηf : DX ⟶ DS`, `ηe : DY ⟶ DT`, `ηg : DT ⟶ DS`, `ηh : DY ⟶ DX`. Pass: naturality supplies exactly the four compatibility equations. |
| Each displayed stage square Cartesian | `sqi i : ChosenCartesianSquare (ηe.app i) (ηh.app i) (ηg.app i) (ηf.app i)`. Pass: its upper-left corner is Y_i, projections e_i to T_i and h_i to X_i. |
| All four systems have affine transitions | The four instance families `IsAffineHom (DX.map a)`, `IsAffineHom (DY.map a)`, `IsAffineHom (DS.map a)`, `IsAffineHom (DT.map a)`. Pass: all transition arrows, with no extra Cartesian-transition requirement. |
| Each g_i is qcqs | The two instance families `QuasiCompact (ηg.app i)` and `QuasiSeparated (ηg.app i)`. Pass: no extra condition on f_i or on the stage schemes. |
| X, Y, S, T are the four limits | `cX`, `cY`, `cS`, `cT` and `hcX`, `hcY`, `hcS`, `hcT`. Pass: specified cones with their universal properties, not arbitrary apex schemes. |
| f, e, g, h are the induced limit arrows | Four morphism binders and `hf`, `he`, `hg`, `hh`. Pass: their projection equations uniquely determine the induced arrows by each target limit property. |
| The induced limit square is Cartesian | `sq : ChosenCartesianSquare e h g f`. Pass: records the Cartesian square already specified by the node. This data always exists by the four limit properties and stage pullback uniqueness. Its chosen pullback isomorphism never enters the conclusion, which uses only `sq.toCommSq`. |
| p_i is the T projection | `cT.π.app (op i)` for forward i. Pass: no independently chosen maps. |
| Abelian sheaves F_i on the small etale sites | `Fi i : Sheaf (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}`. Pass: precisely the recorded abelian-sheaf encoding. |
| Torsion for each F_i | `torsionFi i : CategoryTheory.Sheaf.IsTorsion (Fi i)`. Pass: the actual declaration quantifies over sections and a covering sieve with finite-order restrictions, so it is local torsion as in the node. |
| Coefficient transition a_ji inverse image F_i to F_j | `φ a` for a forward arrow `a : i ⟶ j`, using `DT.map a.op : T_j ⟶ T_i`. Pass: transition is an arbitrary morphism of the required type, not assumed invertible. |
| Identity and composition laws for coefficient transitions | `hφid` and `hφcomp`. Pass: `DT.map_id` transports the identity pullback, followed by `upperStarId.hom`; for a then b, `DT.map_comp b.op a.op` identifies the composite pullback, followed by pullback of `φ a` and `φ b`. The order agrees with a_kj followed by a_ji on schemes. |
| The forward diagram p_i inverse image F_i | `D : I ⥤ Sheaf ...`, `ιF i`, and `hD`. Pass: `ιF` identifies objects and `hD` fixes every arrow. Its `upperStarComp.hom` goes from p_i inverse image to p_j inverse image of a_ji inverse image, using `(cT.w a.op).symm`, then applies p_j inverse image to `φ a`. This is exactly the source's displayed transition. |
| F is the colimit of that diagram | `cF : Cocone D`, `hcF : IsColimit cF`, with F = `cF.pt`. Pass: the source notion is a sheaf colimit; the universal property and `hD` prevent an unrelated coefficient object or unrelated transition diagram. |
| Fixed q at least zero | `q : ℕ`, passed as `(q : ℤ)` to homology. Pass: one degree chosen before all stage hypotheses. |
| Every stage base-change map in degree q is invertible | `hbase : ∀ i : Iᵒᵖ, IsIso (...)`. Pass: the map is homology of canonical `Etale.derivedBaseChangeMapPlus` on `Fi i` in degree zero, on the square `sqi i`. |
| The limit base-change map in the same degree is invertible | The concluding `IsIso (...)`, using `sq.toCommSq` and `cF.pt` in degree zero. Pass: exactly the analogous canonical map on the limit, with no assertion about other degrees. |

For the last two rows I opened `BaseChange/Derived.lean`: its map is
`g^* Rf_* -> Rf'_* g'^*` for `CommSq g' f' f g`.
Substitution `(g',f',f,g) = (e,h,g,f)` therefore gives the required
`f^-1 Rg_* -> Rh_* e^-1`, not the exchange in the other direction.
I read `KunBcMapOnCohomology.lean`, especially the two canonical comparison
isomorphisms around homology of derived exchange. Exact inverse image commutes
with degree-q homology and sends a single sheaf complex to its inverse-image
single complex. Conjugating by those isomorphisms identifies the asserted
`IsIso` with the node's sheaf-level degree-q `IsIso`; the assertion is neither
a mere existence of an abstract isomorphism nor a full derived isomorphism.

Dependency audit: I opened `ChosenCartesianSquare.lean`, the recorded upstream
`EtaleSheaves.lean` encoding (read through `scompile.py --source` because it is
absent from the older local checkout) and `Sheaf.IsTorsion` in upstream
`SheafCohomology/Basic.lean`, `UpperLowerStar/Defs.lean` (lowerStar, upperStar,
the adjunction and upperStarComp), `UpperLowerStar/Coherence.lean`
(upperStarId), and `BaseChange/Derived.lean` (derivedBaseChangeMapPlus).
For the convention and Mathlib leaves I checked Scheme, QuasiCompact,
QuasiSeparated and IsAffineHom, and the fields of Cocone and IsColimit.
The convention node deliberately defines no second scheme notion. These are
all the owning nodes' recorded notions. No new node or dependency module is
needed, so there is no H12/H13 packet to audit. `lem-kun-0eym` still has no Lean
record and is a proof-only dependency; the statement uses none of its objects.
The other recorded proof interfaces are imported, with non-public imports
where appropriate, including the Mathlib mate and homology matches.

Edge cases: the empty index is excluded because a directed set here is
nonempty. A one-element index is allowed. Arbitrary equivalent indices in a
preorder are allowed. q = 0 is included; no negative-degree or full-derived
conclusion is added. Zero sheaves, empty schemes and their morphisms are
allowed. There is no coefficient ring, field, exponent, characteristic,
finiteness, smoothness or properness restriction. Noninvertible coefficient
transitions remain allowed, also over constant scheme systems. The single
universe u is explicitly bound; schemes and the index follow the recorded
index-size convention, and AddCommGrpCat.{u+1} follows the recorded small-etale
abelian-sheaf convention. No equality between distinct site universes is
introduced. All theorem variables are bound with autoImplicit false.

Independent duplicate searches (2026-10-16):

- LeanFinder via msearch: “A base change isomorphism of etale cohomology passes
  to an inverse limit of schemes with affine transition maps”. Eight results:
  affine-limit section descent, etale base-change stability, etale composition,
  Kaehler differentials and pullback-cover identities. None states this theorem.
- Loogle via msearch: `"exchange"`. Twelve results concerning set exchange,
  matroid exchange, and whiskering/natural-transformation exchange laws.
  None states an etale higher-direct-image limit theorem. The preliminary
  two-string query `"baseChange" "IsIso"` was rejected as malformed; no
  negative mathematical conclusion was drawn from that rejected query.
- LeanSearch via msearch: “Canonical etale higher direct image base change
  isomorphisms pass to limits of cartesian squares”. Unavailable with Internal
  Server Error, recorded as unavailable rather than a negative match.
- msearch grep `exchange.*limit|limit.*exchange|baseChange.*limit`: four Mathlib
  hits, all generic precoverage/base-change or monoidal exchange identities.
- Direct rg in Mathlib, upstream WeilConjectures and shared lean/Sheaf for
  `0EZT|higherDirectImage_baseChange_of_limit|baseChange.*[Ll]imit|[Ll]imit.*baseChange`.
  I read the full relevant statements, rather than treating source-tag matches
  as exact duplicates. `Etale.higherDirectImage_limit` fixes S and pulls all
  coefficients from one W; `preservesColimitsOfShape_higherDirectImage` fixes
  the morphism. Project `isIso_limit_homology_derivedBaseChangeMapPlus` and
  `nonempty_limit_derivedDirectImage_single_iso` fix a field base and a single
  source sheaf, and impose further qcqs assumptions. None covers four varying
  systems and the arbitrary compatible Fi of this node.

Mismatch and changes: no mismatch remains in the revised Lean statement. I
left the correct module and node record unchanged and added this independent
second-reading audit. In particular I did not undo the worker's correction of
the coefficient diagram or claim that I made it. The sandbox node differs
from the shared node only in `lean`, with no statement_change. There is no
unit-statement correction, citer audit requirement, disputed flag, definition,
hollow data, private copy or supplied proof in this delivery. The theorem has
exactly one proof, `by sorry`. Its docstring records all five node proof steps,
including canonical-map compatibility. Every line of Lean is at most 100
characters. The node's lean.statement was checked byte-for-byte against the
signature before `:= by`.

Second-reader validation: the prescribed scompile.py wrapper compiled the sole
delivered module cleanly in both sandbox (26.0 s) and library (45.6 s) contexts,
under the default 60-second per-file limit. No error or warning was emitted.
The first invocation used a relative path from the read-only clone; I corrected
it to the absolute sandbox path before compiling. This was an invocation-path
error, not a missing dependency or a statement defect.
