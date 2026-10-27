## Worker report

Delivered statement module: `Sheaf.AlgebraicGeometry.GroupScheme.PotentialSmoothNormalization`.
The only postponed theorem is
`AlgebraicGeometry.PotentialSmoothNormalization.exists_potential_smooth_normalization`.
Its proof is `sorry`. All seven helper constructions have real data; none chooses an
object from an existence theorem. They only name the spectra, scalar arrow, tensor
algebras, integral closure, and canonical normalization arrow belonging to this node.

Source read online: [Prasad--Yu, On quasi-reductive group schemes](https://arxiv.org/pdf/math/0405381),
Section 3.3/Proposition 3.4 and Appendix A, especially Corollary A.4 (printed p.27).
The affine flat model with smooth generic fibre has the stated finite group-smoothening
normalization after a suitable extension. The node's proof additionally obtains a
specified algebraically closed residue field by local extension and completion.
The eight proof steps are included in the theorem docstring with their dependency names.
The source is not present as a local PDF. The current blueprint was searched at
`literature/blueprint/latest/`; the node is an auxiliary split, not a unit statement.

Hypothesis and conclusion correspondence (all helper names below are in
`AlgebraicGeometry.PotentialSmoothNormalization`):

| Node clause | Lean rendering |
| --- | --- |
| A is a DVR | `A : Type u`, `[CommRing A] [IsDomain A] [IsDiscreteValuationRing A]` |
| K is its fraction field | `K : Type u`, `[Field K] [Algebra A K] [IsFractionRing A K]` |
| k is the residue field | `IsLocalRing.ResidueField A` |
| A fixed algebraic closure of k | arbitrary `Ω : Type u`, `[Field Ω] [Algebra (IsLocalRing.ResidueField A) Ω] [IsAlgClosure (IsLocalRing.ResidueField A) Ω]` |
| G = Spec B, affine over A | `affineOver A B = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))` |
| B finitely generated and flat over A | `[Algebra.FiniteType A B] [Module.Flat A B]` |
| Multiplication, identity, inverse and group diagrams over A | `[GrpObj (affineOver A B)]` in `Over (Spec (.of A))` |
| Smooth generic fibre | `hsm : Smooth ((Over.pullback (scalarArrow A K)).obj (affineOver A B)).hom` |
| Geometrically connected generic fibre | `hconn : GeometricallyConnected` of precisely that same generic structure morphism |
| A local injective extension to a henselian DVR R | existential `R`, `CommRing`, `IsDomain`, `IsDiscreteValuationRing`, `HenselianLocalRing`, `Algebra A R`, `IsLocalHom (algebraMap A R)`, followed by `Function.Injective (algebraMap A R)` |
| Residue field identified with the specified closure | `e : IsLocalRing.ResidueField R ≃+* Ω` |
| Compatibility with k -> Ω | `e.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap A R)) = algebraMap (IsLocalRing.ResidueField A) Ω` |
| L = Frac R | the actual `FractionRing R`, with its canonical algebra and fraction-ring instances |
| B_R = B tensor_A R | `coordinateBase A B R = R ⊗[A] B`, the canonically commuted tensor presentation |
| Ambient generic coordinate algebra B_R tensor_R L | `coordinateGeneric A B R = (coordinateBase A B R) ⊗[R] (FractionRing R)` |
| The prescribed closure, elements satisfying a monic equation | `coordinateClosure A B R = integralClosure (coordinateBase A B R) (coordinateGeneric A B R)`; Mathlib defines its carrier by `IsIntegral` |
| Finite B_R-module | `Module.Finite (coordinateBase A B R) (coordinateClosure A B R)` |
| N = Spec C over R | `normalizedModel A B R = affineOver R (coordinateClosure A B R)` |
| An R-group-scheme structure on N | existential `GrpObj (normalizedModel A B R)` |
| N is smooth, affine, of finite type over R | `Smooth` of its structure morphism, `IsAffine` of its source, and `LocallyOfFiniteType` plus `QuasiCompact` of the structure morphism |
| The canonical normalization map ν | `normalizationArrow A B R`, explicitly constructed by `pullback.lift` from Spec of the composite B -> B_R -> C and the structural map Spec C -> Spec R |
| ν is a homomorphism to the given G_R | `IsMonHom (normalizationArrow A B R)`, with target group structure canonically inherited under `Over.pullback` |
| ν_L is an isomorphism | `IsIso ((Over.pullback (scalarArrow R (FractionRing R))).map (normalizationArrow A B R))` |
| Special fibre over the specified Ω | pullback along `Spec.map (CommRingCat.ofHom (e.toRingHom.comp (IsLocalRing.residue R)))` |
| Special fibre is a group scheme | the monoidal pullback functor canonically takes the existential `GrpObj` to a group object; `Functor.grpObjObj` is enabled by the standard `CategoryTheory.Obj` scope |
| Special fibre smooth, affine, of finite type | explicit `Smooth`, `IsAffine`, `LocallyOfFiniteType`, `QuasiCompact` clauses for that pullback |
| ν finite and surjective on underlying spaces | `IsFinite (normalizationArrow A B R).left` and `Surjective` of exactly the same underlying scheme map |
| Special-fibre ν finite and surjective on underlying spaces | `IsFinite` and `Surjective` of `.left` of the pullback functor's image of `normalizationArrow` along the displayed residue arrow |
| Finite means finite coordinate module | `IsFinite` is Mathlib's affine-locally finite coordinate-ring map, not finite underlying point set; the total coordinate module is also asserted explicitly |
| No excellence assumption | no excellence, Nagata, completeness, characteristic, reductivity, or special-fibre connectedness assumption is in the theorem's input |

The supplied K is arbitrary, not fixed to a particular fraction-field implementation.
The output fraction field is named canonically because the node says to put L = Frac R.
All rings and schemes share the arbitrary universe `u`, as required by Mathlib's category
of schemes: any concrete input sizes fit a common universe, and the existential extension
can be built in that same universe. No field-extension test quantifies in a smaller
independent universe; `GeometricallyConnected` is the existing scheme predicate.
No variable or universe is auto-bound (`set_option autoImplicit false`).

Dependency declarations read and used:

| Dependency node | Module / declaration used |
| --- | --- |
| def-sc-discrete-valuation-ring | `Mathlib.RingTheory.DiscreteValuationRing.Basic` / `IsDiscreteValuationRing` (requires `IsDomain`, extends principal ideal and local ring structures, maximal ideal nonzero) |
| def-weil-algebraic-closure | `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, `Mathlib.FieldTheory.IsAlgClosed.Basic` / `IsAlgClosure`, allowing the specified closure instead of only the concrete `AlgebraicClosure` implementation |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme` / `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map` |
| def-weil-pbc-flat-ring-map | `Mathlib.RingTheory.RingHom.Flat` / `Module.Flat` (the algebra form of `RingHom.Flat`) |
| def-sc-group-scheme | `Mathlib.CategoryTheory.Monoidal.Grp`, `Mathlib.CategoryTheory.Monoidal.Mon` / `CategoryTheory.GrpObj`, `CategoryTheory.IsMonHom`; the recorded group scheme convention is used over Spec A and Spec R as the item explicitly instructs |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth` / `AlgebraicGeometry.Smooth` |
| def-weil-connected-scheme | `Mathlib.Topology.Connected.Basic` / `ConnectedSpace`, used inside `AlgebraicGeometry.GeometricallyConnected` from `Mathlib.AlgebraicGeometry.Geometrically.Connected` |
| def-weil-pbc-henselian-terminology | recorded module `WeilConjectures.Mathlib.RingTheory.Henselian` / reexported `HenselianLocalRing` |

Additional existing APIs, without duplicate notions: Mathlib `integralClosure`,
`Algebra.TensorProduct`, `FractionRing`, `Over.pullback`, `Functor.grpObjObj`,
`IsLocalRing.ResidueField.map`, and `AlgebraicGeometry.IsFinite` / `Surjective`.
The module imports the available stated proof dependencies privately, including the new
Raynaud--Faltings and completion/DVR modules. At inspection,
`lem-sfb-finite-normalization-local-dvr` had neither a Lean record nor a Mathlib match;
it is only a proof prerequisite, so no redundant statement or import is invented here.
Its proof role remains explicit in the docstring for stage 3.

Edge cases checked before finalization:

- Zero B / empty G: the group-object input itself requires an identity section from
  nonempty Spec A, so no spurious `Nontrivial B` or nonempty-fibre hypothesis was added.
- Zero-dimensional / trivial group: permitted; no positive dimension, nontriviality,
  reductivity or semisimplicity requirement occurs.
- Residue characteristic 0, 2, or arbitrary positive characteristic: all permitted;
  no characteristic binder constrains A or Ω.
- Imperfect residue field and inseparable field extensions: `IsAlgClosure` retains the
  specified algebraic closure; no separability assumption was introduced.
- Nonexcellent and nonhenselian input DVR: permitted. Only the output DVR is henselian;
  the proof constructs an auxiliary complete DVR rather than requiring A to be complete.
- The special coordinate quotient need not inject into the normalized quotient:
  surjectivity is stated on scheme maps, not encoded by quotient-ring injectivity.
- The residue arrow has direction R -> Ω using `e`, not its inverse; compatibility
  explicitly fixes the original k -> Ω embedding.
- The generic isomorphism and special maps are pullbacks of the same canonical arrow;
  no arbitrary morphism or arbitrary isomorphism replaces ν.

Searches for an existing statement, all through the required wrapper unless noted:

1. `leanfinder`: "An affine flat finite type group scheme over a DVR has a finite smooth
   normalization after local extension of discrete valuation rings". Eight hits, including
   smooth charts and relative normalization; none constructs the required DVR extension.
2. `loogle`: `"normalization", "Smooth"`. One hit,
   `AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth`, which concerns
   commuting normalization with an already smooth base change, not potential smoothness.
3. `grep`: `smoothen|Prasad|Raynaud|normalization` in Mathlib `AlgebraicGeometry`.
   Hits in Normalization/ZariskisMainTheorem only; no statement matching this node.
4. `leansearch`: "An affine finite type flat group scheme over a DVR has a finite smooth
   normalization after extending the DVR". Eight hits on relative normalization,
   smoothness and affine normalization; no matching theorem.
5. `rg` in the exact project roots `lean/WeilConjectures` and `lean/Sheaf` for
   `potential.*[Ss]mooth`, `[Ss]mooth.*[Nn]ormaliz`, `normalization.*group`, and the item id,
   followed by narrower `potentialSmooth|potential_smooth|group_model.*normal|exists.*smooth.*normalization|raynaudFaltings`.
   Existing hits are purity trace normalizations, curve normalizations, and the prerequisite
   `RaynaudFaltingsNormalizedReduction`; none is the group normalization theorem.
6. The prescribed `grep -rn` of the item id in `lean/WeilConjectures` returned no hits.
   The upstream name registry and current blueprint were also searched for the item id.

No new independent notion is needed; no dependency interface repair or statement correction.
No `STATEMENT-DISPUTED` issue remains. The DAG's natural-language statement and proof are unchanged.

## Second reading by Q114

The dispatcher explicitly prohibits starting other agents and assigns independent review
to the maintainer. This section records the worker's second reading, not a claim that a
second agent reviewed the delivery.

Reopened the node and the final Lean file. Matched every hypothesis and conclusion in the
above table, checking the full constructions rather than only the theorem's name. The
first elaboration exposed a residue-arrow direction error; it was repaired to `e.comp
residue`. The canonical pullback arrow's structural square is now checked directly from
ring-map compatibility, with no postponed helper theorem. Enabled Mathlib's standard
`CategoryTheory.Obj` scope so the target group law is the canonical pulled-back law.
Removed the sole unused simp argument. Retained arbitrary K with its fraction-field
instance to match the consumer's input directly. Rechecked that the normalization is
literally the integral closure, not a freely chosen smooth cover, that the special fibre
uses the fixed Ω through the required compatible e, and that finite type includes
quasi-compactness. No mathematical clause was dropped or added.

Compilation and delivery validation: all compiles use the prescribed `scompile.py`,
compiling sandbox and library paths separately. Final clean compile and the mandatory
`deliver2.py --no-push` preflight are recorded by the wrapper output for this delivery.
