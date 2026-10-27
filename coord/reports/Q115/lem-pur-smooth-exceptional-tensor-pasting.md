## Worker report

The module `Sheaf.Paper.SmoothExceptionalTensorPasting` states the clauses of
lem-pur-smooth-exceptional-tensor-pasting in canonical etale-origin coordinates,
with comparison pullback applied to the exceptional equations. These coordinates
are the recorded `def-pur-co-smoothness` interface, not a replacement adjunction
on the ambient pro-etale category. The first conjunct of `squareClause` asserts
invertibility of the live standing comparison-coordinate mate
`standingExceptionalBaseChangeCompared`.
All five theorems have only `sorry` proofs. Every abbreviation and helper has
real data, and every helper is recorded in lean.declarations.

Hypothesis and clause correspondence:

- The finite-field algebraic closure, the distinct prime ell, the finite coefficient
  extension inside the fixed closure, and n >= 1 are exactly the fields of
  `P : WeilConjectures.PurityFiniteSetting`. `P.Coefficient` is the canonical
  universe lift of O_E/(varpi_E^n), including ramified coefficient extensions.
- Every scheme has `Over (Spec (.of P.field.k))`, `LocallyOfFiniteType` and
  `QuasiCompact` on its structure arrow. There is no absolute separatedness
  assumption. Every named arrow is a k-morphism and has `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, matching separated finite type.
  The helper definitions derive Noetherian and compactness instances from the
  structure arrows, and use Nagata instances internally; compactifications
  are not additional hypotheses of the theorems.
- Pure relative dimensions are natural-number parameters with
  `SmoothOfRelativeDimension` instances for h,h',h'' or f,g,a,b as appropriate.
  The composites and base changes inherit smoothness. No orientation is supplied.
- `D`, `L`, `R` and `V` abbreviate the published etale derived category,
  left-derived inverse image, exceptional functor and comparison pullback.
  `Ctf` is the published pro-etale `constructibleFiniteTor` predicate on V(K).
  Quantifying every such etale representative covers every pro-etale Dctf
  object by the recorded constructible-origin statement; no witness is fixed.
- Cartesian squares use Mathlib `IsPullback`. This is equivalent to the recorded
  chosen Cartesian identification: its universal property constructs the
  unique isomorphism to the chosen pullback respecting both projections.
- B is `Etale.rightDerivedUpperShriekBaseChangeMap`, followed by V on arrows.
  Its definition is `mateEquiv` of inverse compact-support exchange under the
  actual etale exceptional adjunctions. The live standing definition
  `standingExceptionalBaseChangeCompared` is precisely this comparison image,
  for the retained compactifications. Its invertibility is the first conjunct
  of `squareClause`; no separate standing-square clause is needed.
- `squareClause` asserts B(K) invertible, and identifies its unit value, after
  applying the canonical pullback-unit map inside R(h'), with the specified
  `Etale.dualizingComplexBaseChangeMap`, namely beta. Its final conjunct is
  the exact published `smoothTensorBaseChangeCoherence` equation. The etale
  theta is omega-first; the symmetry in the node converts it to pullback-first.
- `basePastingClause` asserts successive-base-change pasting. `sq₁.paste_horiz sq`
  is the composite square. The equation inserts the target and source
  `Etale.leftDerivedUpperStarComp` comparisons explicitly, so it is the node's
  B(h,vw)=B(h',w) u'^*B(h,v), with matching endpoints.
- `identityClause` asserts identity-base-change normalization. Both sides use
  `Etale.leftDerivedUpperStarId`; no strict equality of pullback functors
  is presumed.
- `towerClause` first asserts c_(b,a) B_(gf,w) =
  a^! B_(g,w) B_(f,v) u^*c_(g,f). Its c is precisely the dependency's
  `WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition`, the
  adjunction conjugate of `Etale.unboundedEtaleLowerShriekCompIso`.
- `sigma` is the dependency's c inverse after the published theta at omega_g.
  The published omega-first ordering has already absorbed the symmetry in the
  node's formula. The second tower conjunct is D u^*sigma = sigma'(A tensor a^*B),
  with the monoidal pullback map and the derived square comparison displayed.
  In particular it does not substitute `smoothExceptionalCompIso`, which is
  presented using a different compact-support-composition construction.
- `reassociationClause` asserts derived associativity, Koszul symmetry, both
  action units, the threefold pullback equation, tensor/composition
  compatibility, and the tensor and composition localization squares on
  homotopy representatives. The generic coefficient-category parameter keeps
  the actual maps unchanged while avoiding expensive comparison of definitionally
  equal monoidal-instance terms at ModuleCat; the theorem specializes to
  `ModuleCat P.Coefficient`, so it adds no hypothesis.
- `chainReassociationClause` states the corresponding actual chain-map
  associator, Koszul symmetry, left and right unit, and threefold-composition
  equations. The maps are the existing total-complex tensor comparison and
  termwise pullback composition. These hold on all complexes and hence on
  the flat-term K-flat representatives specified by the node. Together with
  the two localization squares this includes the representative-level clause.

Statement dependencies read and used (module and declarations):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`; the coefficient quotient is the actual existing one.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: the reexported
  `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor` and the
  etale/intrinsic presentations of the same finite-Tor category.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `.ProEt.topology`, with object universe u+1 and Hom universe u unchanged.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `WeilConjectures.finiteDerivedPullback`, `.finiteIntrinsicDerivedTensor`,
  `.finiteIntrinsicTensorModels`; the comparison coordinates use the existing
  fixed-ModuleCat operations already used by the recorded co-smoothness interface.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded
  `WeilConjectures.ConstructibleExceptionalCoefficients.System` and reexported
  `AlgebraicGeometry.ProEtale.sfFiniteExceptionalAt`; the actual finite functor
  is nu^* f^times Rnu_* (also read in SfFiniteExceptionalInverseImage).
- `Sheaf.Paper.PurityFiniteExceptionalComposition`:
  `WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition`.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `AlgebraicGeometry.ProEtale.finiteComparedDualizing`, `.finiteComparedTensorClause`,
  `.finiteComparedBaseChangeClause`, `.IsCohomologicallySmoothFiniteCompared`;
  and its published etale `dualizingComplexTensorMap` and
  `dualizingComplexBaseChangeMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`, `.SmoothOfRelativeDimension`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition` and the canonical
  constant-coefficient specialization, with K-flat representative normalization.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  and the small-site `Scheme.ProEtaleTensorModel` and
  `.proEtaleCanonicalTensorComparison`. No site universes are identified.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare` (universal-property presentation above).
- `Sheaf.Paper.StandingExceptionalBaseChangeCompared`:
  `AlgebraicGeometry.ProEtale.standingExceptionalBaseChangeCompared` (Q153);
  its module and node record are retained byte-identical to live.
- `def-weil-scheme-morphism-properties` is a convention collector without a
  declaration; the property classes it names are used directly.

Proof imports retain every available proof-dependency module, including the
cochain coherence, compact-support comparisons, origin/comparison and finite
projection formula statements. The newly landed `Sheaf.Paper.TensorMateBaseChange` is also imported as a
proof dependency. The proof-only DAG nodes without a recorded
module (mate-pasting and adjunction-mate) are named in
proof docstrings; no unstated proof assertion is used to construct data.

Edge cases checked: zero input, empty schemes, identity base change, identity
smooth maps, relative dimension zero, n=1, ramified E, and nonseparated finite-type
schemes. Unit and composite pullbacks are compared canonically, not strictly.
Empty schemes require no chosen point or positive dimension. The coefficient
quotient is never assumed to be a field or flat over a larger coefficient ring.

Searches performed: msearch LeanFinder, query "smooth exceptional inverse image
base change commutes with composition tensor counit mates", returned eight
adjunction/module-pullback facts, none stating this geometric result; msearch
Loogle "CategoryTheory.mateEquiv, CategoryTheory.conjugateIsoEquiv", zero hits;
msearch grep "UpperShriekBaseChange|exceptional.*[Pp]asting" in CategoryTheory,
zero hits. Earlier recovered search log also records LeanFinder and Loogle
mate-pasting queries and a CategoryTheory grep, with no exact match. Direct rg
in Mathlib, WeilConjectures and Sheaf found the canonical etale maps,
UpperStarCompCoherence, UpperStarMonoidal and CohomologicalSmoothnessTheorem;
these supply constituent maps and clauses, not the complete node. An rg of the
item id in WeilConjectures found no declaration. No new independent notion is
introduced, so no new definition node is needed.

No statement correction; no STATEMENT-DISPUTED issue. Compiler errors recovered
from the interrupted draft were repaired (parentheses on map arguments and the
coefficient argument of towerClause). A concrete-ModuleCat reassociation timeout
was repaired by the upstream generic-category presentation, specialized by the
theorem. No timeout limit was raised.

## Second reading by Q115

A second pass in this same worker session read the node and every delivered
signature together (the dispatcher forbids starting other agents). It found and
repaired four omissions in the recovered draft: the final reassociation clause,
its actual chain-level content, the missing live standing-base-change definition,
and an explicit invertibility assertion for that actual pro-etale map.
The returned dependency replacement and redundant assertion are superseded by
the live Q153 comparison-coordinate declaration, as described below. It checked
both directions and endpoints of base-change and tower pasting, the c choice
against the finite exceptional-composition dependency, and the absorbed symmetry
in sigma. It checked each geometric binder against the opening conventions and
verified that no absolute separatedness, orientation or ambient exceptional
adjunction has been added. All helper definitions use published maps. No node
statement has changed and no additional mathematical assumption is imposed.

## Returned-delivery repair

The immutable-head return (398f637250fb, H13/H4) identified a stale replacement
of `pur9-cs-def-bc` after Q153 landed it at a9d5602c. Read the current live
`StandingExceptionalBaseChangeCompared` module and dependency record and
confirmed the module against `scompile.py --source`. Removed both stale
dependency files from this packet, so the live module and record are preserved
byte-identically. The item continues to import the live module.

Dropped `standingSquareClause` and its redundant theorem conjunct, exactly as
requested: its content is the first conjunct of `squareClause`, which maps
`Etale.rightDerivedUpperShriekBaseChangeMap` under comparison pullback, exactly
the live `standingExceptionalBaseChangeCompared` definition. Removed the helper
from `lean.declarations` and updated the recorded main signature verbatim.
No node statement, hypothesis, other clause, or other theorem changed. All
five theorem proofs remain `sorry`. The independent review accepted the rest
of the item, and this repair retains those checked clauses.

The current Q153 `TensorMateBaseChange` proof-dependency module is now imported
with a plain proof import, retaining the live standing definition it also uses.

Compiler self-check: the full module initially exceeded the fixed 60-second
limit while comparing tensor structures. Isolated the imports, geometric prefix,
and tensor declarations using module-mode probes. The diagnostic exposed two
instance-search routes to the cochain monoidal structure. Prioritizing Mathlib's
existing `HomologicalComplex.monoidalCategory` and the symmetric-to-braided
projection aligns the existing canonical structures; no new instance is defined.
Keeping the existing sheaf and derived monoidal structures locally irreducible
and respecting transparency avoids repeated expansion of their localization data.
No map, hypothesis, clause, or compiler limit changes. The full diagnostic module
passed the server's confirmation in 55.1 seconds without warnings.
