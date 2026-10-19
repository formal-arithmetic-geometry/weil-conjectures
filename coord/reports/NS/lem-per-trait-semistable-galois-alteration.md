## Worker report

The module states `AlgebraicGeometry.exists_trait_semistable_galois_alteration`, with
`sorry` as its only theorem proof. It also supplies three concrete helper definitions:
`traitSemistableEquation`, `traitSemistableChartAlgebra`, and
`traitSemistableChartProjection`. These belong to the semistable-chart clause of this
node: they are the polynomial, its principal-ideal quotient, and the Spec map induced
by the constants followed by the quotient homomorphism. No existence theorem or
arbitrary selected data is used to construct them. There are no new independent
notions or dependency repairs, and the node's natural statement is unchanged.

Source read: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XVI §3.7,
printed p.254, first two paragraphs, all four bullets, and the sentence supplying
the generic-fibre log structure and log smoothness. These give the finite group,
finite trait extension, projective regular semistable alteration, equivariance, and
generic Galois cover. The DAG expands this geometric input into seven proof steps;
all seven, including dimension zero, appear in the theorem's proof docstring.

Clause-by-clause correspondence:

- Trait: `R : CommRingCat`, `IsDomain R`, and `IsDiscreteValuationRing R` express
  exactly a Noetherian local one-dimensional domain with principal maximal ideal.
  Mathlib's equivalent local non-field PID formulation does not include fields.
- Complete: `IsAdicComplete (IsLocalRing.maximalIdeal R) R`.
- Strictly henselian: `IsStrictlyHenselianLocalRing R`, the existing class combining
  `HenselianLocalRing` and separably closed residue field. Henselianity is the
  simple-root lifting condition, via its existing standard equivalences.
- Mixed characteristic: `CharZero (FractionRing R)` and `hchar`, existence of a prime
  positive residue characteristic. There is no perfect-residue-field assumption.
- Integral regular X: `[IsIntegral X]` and `hreg : IsRegularScheme X`; the latter
  includes local Noetherianity as stipulated by its dependency node.
- X/S: `s : X ⟶ Spec R`; flatness `[Flat s]`; finite type as the recorded conjunction
  `[LocallyOfFiniteType s] [QuasiCompact s]`.
- Quasi-projective X/S: `hqp` is an immersion into the actual relative projective
  space with `N+1` homogeneous coordinates, and its projection equals `s`.
- Finite group: existential `G : Type u` with `Group G` and `Finite G`.
- Finite dominant complete strictly henselian trait S′/S: existential `A`,
  `IsDomain A`, `IsDiscreteValuationRing A`, its adic-completeness and strictly
  henselian instances, and `t : Spec A ⟶ Spec R` with `IsFinite t ∧ IsDominant t`.
- Integral regular X′: `Y : FineSaturatedLogScheme` and the explicit
  `IsIntegral Y.scheme ∧ IsRegularScheme Y.scheme` conjuncts. The bundled log scheme
  gives precisely the locally Noetherian fs framework of the recorded dependency.
- Finite type over both bases: the separate `LocallyOfFiniteType` and `QuasiCompact`
  conjuncts for `q` and `q ≫ t`.
- Quasi-projectivity over both bases: the two existential immersions into
  `ℙ(ULift (Fin (N+1)); Spec A)` and its counterpart over `Spec R`, with the projection
  equations `= q` and `= q ≫ t`.
- Commutative square: `a ≫ s = q ≫ t`.
- Projective dominant a: `IsHProjective a ∧ IsDominant a`. H-projectivity is precisely
  the blueprint's finite projective-space embedding convention, not an unspecified
  proper morphism or a projective-bundle surrogate.
- Actions and equivariance: `ρY : G →* Aut Y.scheme` and `ρB : G →* Aut B.scheme` give
  the global actions. The three `∀ g` equations express that a and t are invariant
  (trivial actions on X and S) and q is equivariant. `eS` merely identifies the
  underlying scheme of the log base `B` with `Spec A`.
- Nonempty generic connected finite étale G-torsor: `U`, `Nonempty U`, and
  `E : Scheme.GaloisCoverAction G U.toScheme`, with `eE : E.Z ≅ (a ⁻¹ᵁ U).toScheme`.
  `ConnectedSpace E.Z` is explicit. The equation `eE.hom ≫ (a ∣_ U) = E.π` identifies
  the structure map; the equation for each g identifies its action with the
  restriction of ρY. The dependency's cover structure contains finiteness,
  étaleness, surjectivity, simple transitivity on every geometric fibre, and the
  quotient universal property. Thus neither an unrelated torsor nor an unrelated
  action is substituted for the inverse image of U.
- Uniformizer: `Irreducible π`, the existing equivalent uniformizer predicate for
  a DVR (Mathlib deliberately uses this rather than a separate Uniformizer type).
- Semistable charts: for each y, choose n,r with `1 ≤ r` and `hrn : r ≤ n`,
  `V : Y.scheme.Etale`, and an étale map `c` into Spec of the explicit quotient
  algebra. `y ∈ Set.range V.hom` covers Y, and the projection equation says the
  chart is over the same Spec A. Fin r selects exactly the first r coordinates of
  Fin n, and ULift preserves the scheme universe. These are actual standard
  equations, not only an abstract log-smooth chart condition.
- Canonical log structure on S′: an isomorphism from `B.logStructure.monoidSheaf.obj`
  to `divisorialLogPresheaf` of `Spec (FractionRing A) → Spec A → B.scheme`, with
  structural map equal to `B.logStructure.alpha`. This is the prescribed
  `O ∩ j_* O_generic^×`, not an arbitrary log structure on the same scheme.
- Divisorial fs structure on X′: `Y` is fs, and its log presheaf is identified with
  `divisorialLogPresheaf` of the actual generic fibre inclusion `pullback.fst q …`;
  the structural-map equation identifies α too. The existing definition tests
  invertibility of sections after restriction to that fibre.
- Trivial on the generic fibre: the equality of `trivialityLocus` with the range of
  this inclusion states the full precise triviality locus used in the source.
- G-stability: for each g the same underlying automorphism `(ρY g).hom` lifts to
  `EtaleLogHom Y Y`. Structural compatibility and the divisorial structural
  inclusion pin the lift uniquely. Applying this also to g⁻¹ gives the inverse;
  no arbitrary different log structure is used for different group elements.
- Log regularity: `Y.IsLogRegular` from the recorded fs-log dependency.
- Log smoothness: `lq : EtaleLogHom Y B`, `lq.base ≫ eS.hom = q`, and
  `lq.IsLogSmooth` from the recorded log-smooth dependency. The base structure has
  already been pinned to the canonical trait structure.
- No restriction on `Nat.card G`, its divisibility, or invertibility is imposed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogStructure.trivialityLocus`, `FineSaturatedLogScheme.IsLogRegular`,
  and `EtaleLogHom`, including its complete section-map and compatibility fields.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogHom.IsLogSmooth`, whose
  complete chart/comparison definition was read.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, which reuses
  upstream `IsRegular` and includes local Noetherianity.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`, read
  with `scompile.py --source` because the older checkout has no file at that path.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, including the stalkwise
  equivalence documented in its full signature/docstring.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Sheaf.AlgebraicGeometry.NormalScheme`: `Scheme.GaloisCoverAction`; the full
  action, geometric-fibre and quotient fields were read and reused.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite` (affine and finite
  coordinate maps), and `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `IsDominant` (dense range).
- `divisorialLogPresheaf` and `divisorialStructuralMap` are the existing definitions
  in `Sheaf.AlgebraicGeometry.LogRegularPair`, imported by the fs-log dependency.
  `IsDiscreteValuationRing`, `IsAdicComplete`, `IsStrictlyHenselianLocalRing`, and
  `FractionRing` are reused from the established ring interfaces.

Every already stated proof dependency is imported in its recorded module. The
three still unstated proof nodes (normal-projective compactification, marked
nodal alteration, marked-nodal semistable modification) have no module to import;
their IDs are retained in the detailed proof docstring and their DAG edges remain.

Edge cases checked:

- An integral X is nonempty; its generic-torsor open is expressly nonempty. Neither
  an empty cover nor an empty group can satisfy the conclusion accidentally.
- Relative dimension zero and X entirely in the generic fibre remain allowed:
  r=n=1 gives A[t]/(t-π), and its generic open has trivial divisorial log structure.
- n=0 or r=0 cannot be used as semistable charts since `1 ≤ r ≤ n` is explicit;
  the projective-space dimension N can be zero as required.
- The group can be trivial, act nonfaithfully on the trait, and have order divisible
  by the residue characteristic. The torsor forces generic faithfulness on X′.
- Nonperfect separably closed residue fields are allowed.
- All rings, spectra, chart variables and geometric test fields live at the same
  scheme universe u. Finite groups can be represented at u; no independent small
  geometric-test universe restricts or vacuously weakens the assertion.

Searches made (the actual msearch queries are recorded in searches.jsonl):

- LeanFinder: “An integral quasi projective scheme over a complete mixed
  characteristic discrete valuation ring has a regular semistable Galois alteration
  after finite extension”. Eight results concerned Weierstrass reduction, finite
  global sections, normalizations and Galois fraction fields; none states this item.
- Loogle: `IsDiscreteValuationRing, IsStrictlyHenselianLocalRing, IsHProjective,
  FineSaturatedLogScheme`. No hits; the service does not know the project-only
  identifier IsStrictlyHenselianLocalRing.
- msearch grep: `Semistable|StrictlyHenselian|DiscreteValuation`, restricted to
  Mathlib/AlgebraicGeometry. Seven hits concern elliptic reduction and order of
  vanishing, with no semistable-alteration statement.
- LeanSearch: “A semistable Galois alteration exists over a complete strictly
  henselian trait”. Eight hits concern Galois field extensions and formal étaleness,
  not a matching theorem.
- `rg` of the source project and `lean/Sheaf` for trait, semistable, projective,
  quasi-projective and the item ID found the downstream prime-to-ell alteration
  and tame quotient interfaces. These are different statements, and importing the
  downstream consumer would reverse its DAG dependency. No declaration is reused
  under an incorrect existing:true record.
- The upstream `IsQuasiProjective` was read: it is only over a field. This theorem
  instead writes the same immersion condition inline over the trait, as the
  already published prime-to-ell consumer does. No duplicate named predicate is
  introduced. The existing curve semistability definitions are only for relative
  curves; the concrete polynomial helpers here express arbitrary dimensions.

No statement correction or STATEMENT-DISPUTED issue was found. The node's natural
statement and all existing dependency records are unchanged. A clean scompile
run succeeded for both the sandbox file and its library module before packaging;
final dry-run and delivery validate the exact final file again.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
