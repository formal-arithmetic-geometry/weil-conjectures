## Worker report

The theorem `AlgebraicGeometry.AlgebraicSpace.exists_rigidifiedSpacePicard` states the
unchanged node in `Sheaf.AlgebraicGeometry.RigidifiedSpacePicard`. Its sole proof is
`sorry`. The separate definition module `RigidifiedPicardRepresentation` packages the
missing general representing property. No definition contains postponed data, no
extra theorem is introduced, and no statement correction is needed.

Hypotheses and conclusions, clause by clause:

* The scheme S is explicitly universe-bound: `{S : Scheme.{u}}`.
  `[IsLocallyNoetherian S]` is precisely local Noetherianity; it is imposed only on
  the original base, never on parameter schemes or changed bases.
* `A : Poincare.Pointed (groupSpaceBase S)` supplies X, f = A.p, e = A.e and
  `A.section_eq : A.e ≫ A.p = 𝟙 _`. These are algebraic spaces and actual maps,
  with no group structure, smoothness, relative dimension or scheme assumption on X.
* `hp : MapIsProper A.p` means separated, finite type and universally closed,
  exactly as spelled out in the node. `hf : MapIsFlat A.p` is the published
  compatible-etale-chart predicate. `hfp` is local finite presentation together
  with quasi-compactness of f and its diagonal, hence finite presentation.
* `hgeom` quantifies over all algebraically closed fields `K : Type u` and all
  `s : Spec K ⟶ S`. Its actual sheaf fibre product is irreducible on the
  published point topology (`IrreducibleSpace` includes nonemptiness) and reduced
  on every etale scheme chart. No hypothesis that the fibre be a scheme is added.
* `UniversalStructureIso A` asserts `IsIso (moduleStructureMap (snd A.p b))`
  for every algebraic-space parameter. In particular it supplies the canonical
  O_T → (f_T)_* O_(X_T) isomorphism for every scheme T. The map is the existing
  chart-normalized structure map, not an arbitrary isomorphism.
* The existential P is an `AlgebraicSpace S` with its existing structural map,
  and `G : CommutativeSpaceGroup P` gives an actual natural commutative group
  law. `MapIsSeparated` and `MapIsLocallyOfFinitePresentation` give exactly the
  asserted properties of P → S; no quasi-compactness of P is asserted.
* U is an actual module on the small etale model of X ×_S P. `IsLine` is the
  original `IsLineModule` transported through the published equivalence
  `smallModuleEquivalence`. The change of model preserves the module universe.
  `rU.left` is the universal rigidification on e × P; `rU.right` trivializes
  the family at zero, and `rU.intersection` makes these trivializations agree.
* `RepresentsAllRigidifiedLines` requires U to be a line and quantifies over
  EVERY algebraic-space parameter T, line L on X_T and specified section
  trivialization r. `∃! a, Poincare.Classifies ... a` asserts existence and
  uniqueness of the map T → P, together with a line isomorphism from the actual
  pullback of U to L respecting r. `Classifies` includes the equality over the
  base and uses the canonical normalized pullback compositors. This is a natural
  representation because its classifying predicate is actual universal-family
  pullback; no arbitrary bijection is substituted. Scheme parameters are included
  via `schemeSpace`, and algebraic-space parameters include T = P.
* `AllRigidifiedAutomorphisms A` states that every line automorphism preserving
  any specified rigidification equals `Iso.refl L`, for all algebraic-space
  parameters. Together with the preceding classification this also gives uniqueness
  of its rigidified isomorphisms.
* `PicardTensorLaw` uses the existing natural group multiplication `addition P G`
  on the actual fibre product P ×_S P and the literal module tensor `L ⊗ M`.
  It asserts that multiplication of classifying maps classifies this tensor.
  The tensor rigidification may be existential: under UniversalStructureIso,
  every two choices of trivialization of e_T^*(L ⊗ M) differ by a unique unit
  pulled back from T, hence define the same rigidified isomorphism class.
  Thus this is exactly the tensor group law on classes. The zero section is
  `G.identity`, used in `pointedGroup P G`; its universal restriction is
  trivialized by `rU.right` with normalization at e from the intersection law.
* `AllRigidifiedPicardBaseChange` quantifies over every `T : Over S`, with no
  Noetherianity assumption. `Pointed.baseChange` is the actual sheaf fibre
  product with pulled-back section. `baseChangeProductMap` and
  `smallModuleTensorPullback` give the actual pulled-back U. `IsBaseChangedAxes`
  fixes its two rigidifications as their actual normalized pullbacks. These data
  again satisfy the all-space classification. With any other representing data,
  `DualComparison` supplies an actual isomorphism over the base preserving zero
  and the universal rigidified module; `Nonempty` and `Subsingleton` assert its
  unique existence, encoding identity and iterated-comparison coherence.
* In particular take T = Spec K, with K algebraically closed and any geometric
  point into S. This same base-change predicate represents all rigidified lines
  of the geometric fibre on all K-scheme parameters (viewed over S), which is
  the ordinary rigidified Picard functor; it is not restricted to degree zero or
  fibrewise algebraic equivalence. This is the node's final fibre clause.

Dependency declarations used (source signatures and docstrings read):

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
* `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, the scheme interpretation of invertible modules.
  The actual space line predicate is the existing etale `IsLineModule`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`, `IsLineModule`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`,
  `moduleTensorSection`, with their normalized chart-limit specification.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`: `moduleStructureMap`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, `MapIsSeparated`.
* `Sheaf.AlgebraicGeometry.RegularGroupSpace`: `groupSpaceBase`, `groupSchemeMap`,
  `groupSpaceProjection`, `CommutativeSpaceGroup`, its `identity`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallModuleEquivalence`, `smallModuleRestriction`.
* `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`: `smallModuleTensorPullback`.
* `Sheaf.AlgebraicGeometry.AbelianSpacePoincareData`: `Poincare.Pointed`, `product`,
  `fst`, `snd`, `parameterSection`, `Axes`, `Classifies`, `pointedGroup`,
  `addition`, `Pointed.baseChange`, `baseChangeProductMap`, `IsBaseChangedAxes`,
  `DualComparison`, `IsLine`, and the `smallMonoidal` instance. These definitions
  themselves are general; none asserts the neutral-component restriction.
  The existing `Represents` is deliberately NOT used: it includes a fibrewise
  algebraic-triviality condition absent from this item.
* `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `enlargedFibreProduct`,
  owned by the landed definition node `def-sfb-space-sheaf-fibre-product`.
* The point topology and quasi-compactness are the existing `Point` and
  `MapIsQuasiCompact` (definition owners `def-a1-space-point-topology` and
  `def-sfb-proper-curve-moduli`). Reducedness of chart schemes is Mathlib's
  `AlgebraicGeometry.IsReduced`.

All available proof-dependency modules are imported. The following proof nodes
have no recorded declaration in the read clone and are not needed to type the
statement: space-geometric-h0, space-picard-sheaf-representability,
space-fppf-qcoh-descent, space-fppf-invertible-locality,
space-valuation-line-triviality and space-valuative-separatedness (each with
prefix lem-sfb-). No new statement duplicates these proof prerequisites.

Edge cases checked before writing: the empty original base is permitted; no
geometric point is required to exist. Over a nonempty base the geometric fibre
condition excludes empty fibres via IrreducibleSpace. Arbitrary characteristics,
singular integral fibres, non-scheme X and P, nonreduced/non-Noetherian parameter
schemes, and non-flat scheme base changes are all admitted. The full Picard space
need not be quasi-compact. All test fields and schemes use the same universe as
S, with no independent smaller test universe, and all variables and universes
are explicitly bound with autoImplicit and relaxedAutoImplicit disabled.

Searches made:

* msearch leanfinder: "A proper flat algebraic space with geometrically integral
  fibres and a section has a separated Picard space representing rigidified line
  bundles". Eight scheme separatedness/AffineSpace hits; no match.
* msearch leansearch: "Relative Picard algebraic space classifies rigidified
  invertible modules on proper flat integral families". Eight CommRing.Pic or
  relPic hits; these classify ring modules and are not this statement.
* msearch loogle: `"AlgebraicGeometry", "Picard"`. Zero hits.
* msearch grep: `Picard|rigidifi|picardFunctor`. Twenty-three Mathlib hits,
  ring Picard groups and unrelated analytic Picard-Lindelof declarations.
* rg of WeilConjectures for the node id: no result. rg rigidified/Rigidified of
  WeilConjectures and Sheaf found RigidifiedLines and AbelianSpacePoincareData;
  their components are reused as above. All five new predicate names and the
  theorem name were checked against Mathlib, WeilConjectures and Sheaf: no hits.
* `tools/blueprint_refs.py search rigidified` found three scheme blueprint nodes
  (det-picard-f-representable-chart, det-picard-main-degree,
  det-picard-pic-split-pairs). None supplies the all-line algebraic-space
  universal representation predicate. DAG text search found this item and
  algebraically-trivial-line-multiplicativity, not a matching definition.

Sources opened: Stacks quot.tex Tags 0D28, 0D2B, 0D2C, spaces-perfect.tex Tag
0E0S, moduli.tex Tags 0DNI and 0DNJ. The six-step source-based proof plan is
preserved in the theorem docstring. No STATEMENT-DISPUTED flag or node fault.

Validation: both delivered modules were compiled separately, in dependency order,
with scompile.py against the server's published live library; clean, including
library module mode (definition module 7.2 s, theorem module 2.6 s). No probe or
local build is part of this delivery.

## New nodes

`def-sfb-rigidified-picard-representation` owns the five genuine Prop-valued
definitions in `Sheaf.AlgebraicGeometry.RigidifiedPicardRepresentation`:
`RepresentsAllRigidifiedLines`, `AllRigidifiedAutomorphisms`,
`UniversalStructureIso`, `PicardTensorLaw`, `AllRigidifiedPicardBaseChange`.
It defines the full rigidified Picard representing property over all space
parameters, its tensor law and arbitrary scheme-base-change compatibility.
Sources are Stacks 0D25, 0D28, 0D2B, 0D2C with etale descent on the parameter.
The recorded three search kinds found no existing equivalent interface:
Poincare.Represents is restricted to algebraically trivial families and scheme
parameters, and Poincare.UniversalBaseChange assumes locally Noetherian changed
bases. Existing pointed spaces, axes, canonical maps and comparisons are reused.
All new definitions have real data; none chooses a representing space or line.
The item cites this new definition node and the landed definition owners of its
other statement components. Its original statement and proof are unchanged.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
