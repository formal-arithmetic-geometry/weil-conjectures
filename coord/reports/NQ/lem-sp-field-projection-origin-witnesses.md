## Worker report

The module `Sheaf.Paper.FieldProjectionOriginWitnesses` states
`AlgebraicGeometry.ProEtale.FieldProjectionOrigin.field_projection_origin_witnesses`.
Its only postponed proof is that theorem. Definitions have actual terms. The natural
index n denotes positive exponent n+1 throughout the existing tower interfaces.

Hypothesis and clause correspondence:

- The global finite-field datum and prime distinct from its characteristic are
  `P : PurityFiniteSetting`; `P.field` and `P.coefficients` carry exactly these
  data. `Index P` is the existing finite-intermediate-field subtype of the fixed
  coefficient closure. `E F : Index P` and `h : E ≤ F` allow every finite field
  inclusion, including the identity and ramified inclusions.
- `X Y : Scheme.{u}`, their `Over` instances, and `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` on the structure morphisms express separated
  finite-type k-schemes. `f.IsOver` expresses a k-morphism.
  `d : ℕ`, `SmoothOfRelativeDimension d f`, and `IsSeparated f` express the
  complete morphism hypothesis, including d=0 and empty source.
- `D : FieldShriekSystem.Models P` is the already specified, section-preserving
  presentation of the ordinary derived strict coefficient towers, their actual
  scalar functors, and geometric operations. The same `c : Compactification f`
  occurs for every coefficient. `b : FieldShriekSystem.Laws P D c` is the
  proper-mate/open-tensor comparison, not arbitrary b.
- `a : FieldExceptionalSystem.Domains P D c` restricts those operations to
  `N P D E T`; its definition uses the recorded normalized constructible
  uniform-cohomological-and-Tor predicate. `A : Adjoints ...` and
  `l : FieldExceptionalSystem.Laws ...` are the specified tower adjunctions,
  finite normalizations, and exceptional comparison laws of the dependency.
  Its `component` is literally the counit transpose required in the node.
- `J` reuses `SpTowerClasses.unit` on the existing `spCoefficientCommRings`.
  The theorem concludes membership `j` of these coefficient units in N; this
  is not a new input assumption. `coefficientUnitMap` is the map determined
  by the global section 1. `scalarUnitMap` is its actual derived
  scalar-adjunction transpose; its invertibility `units` is also a conclusion.
- `K : N P D E Y` and the hypothesis in `WitnessLaws` saying that every
  `(Ev ... n).obj K.obj` has `HasProEtaleTorAmplitude ... s t` express the
  common Tor interval [a,b], renamed [s,t] to avoid shadowing comparison data.
  The pro-etale predicate already includes s ≤ t.
- `HasOriginIn` retains a `SpTowerShriek.Origin`, hence its bounded-below
  fixed-scalar pro-etale level, `FixedEtaleOriginWitness`, and specified
  intrinsic realization isomorphism. It adds bounded constructibility and
  `Etale.DerivedCategory.hasTorAmplitudeIn` of that retained etale complex.
- The first fivefold conjunction of `WitnessLaws`, separately for every n,
  is respectively K, G_E J_E, scalar K, G_F J_F, scalar G_E J_E. Its five
  intervals are [s,t], [-2d,-2d], [s,t], [-2d,-2d], [-2d,-2d].
- The next five clauses `∃ m : ℤ, ...IsGE m` are boundedness below of exactly
  those five ordinary tower-derived objects, independently of level n.
- The next fivefold levelwise conjunction consists of the exact
  `SpTowerShriek.GoodLevel` predicates used in `Laws.projection_iso` of
  det-sp-tower-shriek-levels. Together with the retained origins and the
  preceding lower bounds these supply both inputs for (K,omega_E),
  (scalar K,omega_F), and (scalar K,scalar omega_E), with the X input first
  in that API. The same scalar K is used in both latter pairs.
- `dualizingComparison` is the existing exceptional natural iso at J_E,
  followed by G_F of the canonical scalar-unit iso, precisely inserting
  C_Y J_E = J_F. `transportOrigin` keeps the given etale complex, comparison
  witness, and intermediate fixed-scalar level; its realization is
  `w.realization ≪≫ Ev.mapIso e`. The final universal clause applies it
  to the inverse of this exact dualizing comparison, for EVERY given
  bounded-below omega_F origin. It states bounded constructibility and
  [-2d,-2d] for its retained antecedent. There are no transition conditions
  on origins and no assertion of a strict tower of etale representatives.
- Ramification is unrestricted. `SpTowerShriek.R` is O_E/(ell)^(n+1), not
  the exponent-one uniformizer quotient; `Base.ideals` and
  `Base.ramification_eq` identify it with the h_E(n+1) uniformizer level.
  The existing `GoodLevel` explicitly performs that quotient transport.

Dependency declarations read and used (including their defining interfaces):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its imported coefficient
  ring/integer/uniformizer constructions.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`, `SmoothOfRelativeDimension`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `hasTorAmplitudeIn`; bounded
  constructibility uses the imported standard `isBoundedConstructible`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`,
  `spEllIdeal`; `SmoothPurityCoefficientTowersAbelian`:
  `SpCoefficientTowersAbelian`, `spCoefficientCommRings`, and exact evaluation.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`:
  `spNormalizedConstructibleTorTowers`, `spFiniteConstructibleTor`.
- `Sheaf.Paper.SemilinearDerivedSections` and its public system models:
  `SemilinearDerivedSectionsData`, actual `ScalarData`, `res`, and
  coefficient-system localization. No tower of derived objects is substituted.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: recorded twist
  conventions, reexported through the comparison models; there is no twist
  expression in the final statement apart from the dualizing degree interval.
- `Sheaf.Paper.SmoothPurityTowerGluing`: `SpTowerGluing.tower_gluing`.
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `SpTowerShriek.Origin`,
  `GoodLevel`, `Ev`, `Base`, `Laws.projection_iso`.
- `Sheaf.Paper.FieldShriekSystemComparison`: `Models`, `normalized`,
  `FieldShriekSystem.Laws` and its specified comparison iso.
- `Sheaf.Paper.FieldExceptionalSystemComparison` and its public interface:
  `Domains`, `N`, `scalar`, `Adjoints`, `component`, `iso`, and `Laws`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `Scheme.FixedEtaleOriginWitness`, with its retained complex and iso.
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`:
  `Scheme.finiteRing_constructibleDerived_origin`.
- `Sheaf.Paper.ComparisonTorAmplitude`: the preserving and reflecting
  finite-coefficient comparison theorems.
- Added landed definition dependency `def-sp-tower-class-systems`, module
  `Sheaf.Paper.TowerClassSystems`: `SpTowerClasses.coefficient`, `unit`.
  This owns the existing degree-zero coefficient unit and prevents duplication.

Proof-only imports record chart admissibility, finite admissible coordinate
cover, Tor-interval local detection, scalar normalization, and site comparison.
The theorem docstring spells out all seven DAG proof steps and their uses.

Edge cases checked before drafting: d=0 gives degree zero; empty X or Y
makes the level vanishing assertions valid; K=0 admits any ordered Tor
interval; E=F is retained; positive level one is natural index zero;
ramified h_E,h_F > 1 keep the actual ell quotients; no independent site
universe is collapsed. An arbitrary initially D+ witness is covered by the
last universal clause and its same etale object is retained under transport.
No statement correction, disputed statement, new node, or dependency repair.

Searches run:

- msearch leanfinder: “Bounded constructible etale origin witnesses with
  prescribed Tor amplitude for scalar extensions of dualizing coefficient
  towers”: 8 hits, all unrelated etale algebra facts, no exact match.
- msearch loogle: `AlgebraicGeometry.Scheme, DerivedCategory`: 0 hits.
- msearch grep: `EtaleOrigin|TorAmplitude|dualizing`, AlgebraicGeometry:
  0 Mathlib hits.
- msearch leansearch: “Bounded constructible etale origin witnesses with
  prescribed Tor amplitude for dualizing coefficient towers”: 8 hits;
  derived-category bounded representative existence and unrelated etale
  algebra results, none says this theorem.
- rg of WeilConjectures for the item id and of both project roots for
  `field_projection_origin|projection_origin_witness`: no existing theorem.
- rg of Sheaf for `FixedEtaleOriginWitness`, `GoodLevel`, and unit/scalar
  constructions found the reused Origin, FixedEtaleOriginWitness,
  SpTowerClasses.unit, and specified exceptional-comparison interfaces.

Validation: prescribed server scompile passed cleanly in 18.4 seconds (sandbox)
and 12.5 seconds (final module name). The first two compiler attempts found
only elaboration issues in the coefficient-unit construction: a name collision
was fixed by qualifying FieldShriekSystem.coefficientMap, and the section 1
received its explicit target ring type. No mathematical statement changed.
The prescribed deliver2 dry run passed preflight and compilation (commit
a19b450f294); the packet contains exactly the module, item node, and this report.

## Second reading by NQ

No second worker was started: the assignment explicitly prohibits spawning
agents. The maintainer performs the independent reading after delivery.

## Returned-delivery repair

Repair of H2 on immutable delivery ab90323dfb1b: added the following seven
already-published definition nodes to the item's `stmt_deps`, as requested by
the independent maintainer review. No Lean declaration, hypothesis, conclusion,
proof dependency, or other node field changed in this repair.

- `def-sp-field-shriek-system-models`: module
  `Sheaf.Paper.FieldShriekSystemModels`; declarations
  `FieldShriekSystem.Index`, `Models`, `normalized`, and `coefficientMap`.
- `def-sp-field-exceptional-system-domains`: module
  `Sheaf.Paper.FieldExceptionalSystemDomains`; declarations
  `FieldExceptionalSystem.Domains`, `N`, and `scalar`.
- `def-sp-field-exceptional-system-adjoints`: module
  `Sheaf.Paper.FieldExceptionalSystemAdjoints`; declaration
  `FieldExceptionalSystem.Adjoints`.
- `def-sp-field-exceptional-system-laws`: module
  `Sheaf.Paper.FieldExceptionalSystemLaws`; declaration
  `FieldExceptionalSystem.Laws`.
- `def-sp-field-exceptional-system-iso`: module
  `Sheaf.Paper.FieldExceptionalSystemIso`; declaration
  `FieldExceptionalSystem.iso`, used in `dualizingComparison`.
- `def-weil-proetale-tor-amplitude`: module
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`; declaration
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`. Its existing citation in
  `proof_deps` is retained; its use in the signature also requires `stmt_deps`.
- `def-coef-semilinear-system-models`: module
  `Sheaf.Paper.SemilinearSystemModels`; declaration
  `WeilConjectures.SemilinearSections.systemRing`.

The field-system names above have namespace prefix
`AlgebraicGeometry.ProEtale`. Their recorded declarations and docstrings were
read; existing imports already supply them. Compared the retained returned
packet with current main: before this repair only `lean` and the previously
added `def-sp-tower-class-systems` statement dependency differ. The delivery
wrapper will build the repaired packet against current main. The Lean source
is byte-identical to the reviewed delivery (SHA256
`d16ca8bc9c25b51e85f2e166f93accfb306dbfdd5fcb2a2bfcf00d3048c11578`).

The independent review approved all five origins and their exact intervals,
the five lower bounds, five `GoodLevel` conclusions, canonical adjunction
transpose and comparison direction, and all reported edge cases. H11 was
advisory under the dispatcher's prohibition on starting a second worker.
Fresh prescribed server compilation passed cleanly: 26.8 seconds for the
sandbox module and 25.2 seconds for the final library module. The delivery
dry run and push follow this metadata repair.
