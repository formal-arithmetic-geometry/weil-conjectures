## Worker report

The module `Sheaf.TraceFormula.FiniteFibreValuationDomination` states
`AlgebraicGeometry.finite_fibre_valuation_domination`, with its entire proof `sorry`.
It includes four real helper definitions belonging to the valuation-centre interface
of this node. No theorem is proved. No statement correction or new node is needed.

Hypothesis and clause correspondence:

- `A : HorizontalValuationBase.{u}` supplies the valuation domain V, its specified
  fraction field K, `IsSepClosed K`, finite `PrimeSpectrum V`, and the prime-chain
  condition. Its fraction-field algebra embeds V in K; this is equivalent to the
  stated valuation subring presentation. `A.T` and `A.genericMap` are the actual
  `Spec V` and `Spec K → Spec V`.
- `c : C ⟶ A.T`, `hcurve : RelativeCurve c` supplies flatness, local finite
  presentation, quasi-compactness and quasi-separatedness (together finite
  presentation), and pure dimension one of every scheme-theoretic fibre. There
  is no separatedness or properness requirement on c.
- `hnormal` asks exactly for domain and integral-closure conditions on every
  local ring, without imposing irreducibility or nonemptiness on C. The unrelated
  project `IsNormalScheme` predicate includes integrality and is not used.
- `hsmooth : Smooth (pullback.snd c A.genericMap)` states smooth generic fibre;
  `hcomponents : (irreducibleComponents C).Finite` states finite components.
- `q`, `hq : SchemeModification q`, and `hW : IsReduced W` render the arbitrary
  reduced-source modification W → C. `SchemeModification` includes properness and
  an isomorphism on schematically dense source and target opens; its existing
  `SchematicallyDenseOpen` means injectivity of restriction on every open.
- `ComponentCenteredValuation C` bundles an actual component generic point,
  `ValuationSubring (C.residueField generic)`, the specified spectrum morphism,
  and the existing `IsCenteredValuation` equation. At a component generic point
  of a reduced scheme the residue field is canonically the local ring of the
  reduced component, its function field. Thus no arbitrary field or generic map
  has replaced the specified objects. The centre is `ν.map` of the closed point.
- `ν.residualDegree c = 1` is transcendence degree for the actual residue-field
  map of `ν.map ≫ c` at the closed point of Spec O. This computes exactly the
  stated degree over κ(O intersect K): if s is the image in Spec V, O contains
  V_s, and O intersect K equals V_s. Indeed, every element outside V_s has its
  inverse in the maximal ideal of V_s, which maps into the maximal ideal of O
  because Spec O → Spec V factors locally at s; such an element cannot lie in O.
  Consequently κ(s) is canonically κ(O intersect K). The closed-point residue
  field of Spec O is canonically O/m_O. The algebra structure is specifically
  `((ν.map ≫ c).residueFieldMap ...).hom.toAlgebra`, so there is no unspecified
  residue-field embedding and no new assumption on valuations.
- `∃ F : Set (ComponentCenteredValuation C), F.Finite` is the finite test set;
  each member has residual degree one and closed centre via `IsClosed {ν.centre}`.
- In the first conjunct, p is any modification and its source has normal local
  rings. The hypothesis `∀ ν ∈ F, ∃ l, ...` says each specified valuation has a
  lift with a centre generic in its T-fibre. Uniqueness is supplied independently
  by the next conjunct, so this is precisely the centre on the unique lift.
- `∃ h, h ≫ q = p ∧ SchemeModification h ∧ ∀ h', ...` supplies a C-map which
  is a modification, and uniqueness among ALL C-maps, rather than only among
  maps separately assumed modifications.
- The second conjunct quantifies over every reduced-source modification and
  EVERY component-centred valuation, without a residual-degree or closed-centre
  restriction. `∃! l, l ≫ p = ν.map` gives the specified unique lift. For every
  such lift, a closed original centre implies `IsFibreGenericPoint ... ∨
  IsClosed ...`, exactly the requested dichotomy. The image in T need not be closed.
- `IsFibreGenericPoint f x` uses `f.asFiber x` and a component in `f.fiber (f x)`.
  It refers to the fibre through x, not to the generic fibre or total-scheme
  generic point; it imposes no extra dimension or closedness condition.
- The final conjunct quantifies independently over B, B', b, and r, with exactly
  relative-curve, normality, smooth-generic-fibre, reduced-source modification
  hypotheses. It does not require a separately supplied finite-components
  hypothesis on B. Every fibre-generic x has an open U containing it with
  `IsIso (r ∣_ U)`. For any specified valuation with such an original centre and
  any lift, the lifted centre is fibre-generic. Unique existence of these lifts
  follows by the same second clause applied with the original curve B (or directly
  by the proper valuative criterion); the persistence clause does not select a lift.

Dependency declarations used:

- `Sheaf.TraceFormula.ValuationHorizontalCurveModels`:
  `HorizontalValuationBase`, `.T`, `.genericMap`, `RelativeCurve`.
- `Sheaf.TraceFormula.Modification`: `SchemeModification`, using
  `Sheaf.TraceFormula.SchematicallyDenseOpen.SchematicallyDenseOpen`.
- `Sheaf.AlgebraicGeometry.CenteredValuation`: `IsCenteredValuation`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`; the usual `Field` class.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`; its `IsIntegral` and
  the generic-component residue-field description identify component function fields.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FinitePresentation`, `.Smooth`,
  `.Proper`: `Flat`, `LocallyOfFinitePresentation`, `Smooth`, `IsProper`, inherited
  through the published curve and modification definitions.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`; the published pure
  dimension predicate used by `RelativeCurve` uses topological Krull dimension.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain`, for the inline local normal-domain conditions.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`; `Mathlib.RingTheory.AlgebraicIndependent.Basic`:
  `Algebra.trdeg`.

The three already landed nodes for the valuation interface, modification interface,
and horizontal curve/base interface are added to stmt_deps. There is no duplicated
notion and no new definition node. General component bundling and fibre-centre
helpers are listed in lean.declarations, with source and blueprint docstrings.

Available proof modules are imported without public: ClosedPointField,
ClosedPointsProduct, FiniteBirationalNormalIso, LocallyQuasiFiniteRelativeDimension,
NagataSketchClosure, Mathlib.ValuativeCriterion and Mathlib.ZariskisMainTheorem.
These supply the recorded proof-dependency statements, proper base-change/closed-
immersion instances and proper locally-quasi-finite finiteness. The dependency
lem-trf-modification-fibre-centre-finite has no recorded module yet, so no import
is invented for it; its proof use is explicitly retained in the theorem docstring.

Edge cases checked: empty C and hence empty test set; identity modifications;
a base valuation of height zero (V a separably closed field); disconnected normal
curves with multiple components; nonclosed base points beneath closed centres;
valuations whose original centres are not closed; unrestricted reduced/non-normal
modifications in the lifting clauses; no separatedness of the curve, only the
relative separatedness included in proper modification maps. All schemes, rings,
component fields and valuation spectra use the same universe u, with no independent
smaller test universe. All variables and universes are explicitly bound; both
implicit-variable options are disabled.

Searches made:

- msearch leanfinder: "Finite fibre valuations detect domination of modifications
  of normal curves over a finite height valuation ring". Eight hits, chiefly
  Weierstrass minimal/reduction lemmas and the valuative criterion; no finite test.
- msearch loogle: `"ValuationRing", "IsProper"`. Zero hits.
- msearch grep: `valuation.*modification|Valuation.*Modification|CenteredValuation`.
  Zero Mathlib hits.
- msearch leansearch: "centred valuations on components of a curve with residual
  transcendence degree one finite domination test". Eight valuation/Dedekind
  residue-field hits; no statement matching this node.
- rg in WeilConjectures and lean/Sheaf for valuation structures, SchemeModification,
  residual transcendence degree and centred valuations: found and read the
  existing general IsCenteredValuation, SchemeModification, HorizontalValuationBase
  and RelativeCurve interfaces. The strict-semista​ble-specific CenteredValuation
  requires a strict curve and a closed centre, so it cannot render this theorem's
  arbitrary normal curve and arbitrary-centre lifting clauses. It is not copied.
- rg of the upstream source for the item id, and rg of Mathlib, upstream and side
  modules for the new full names: no existing theorem or collision.
- Read the node, all stmt_deps and their records, recorded source declarations,
  all available proof modules, and Temkin's primary PDF pp. 26--28 online.
  No repair note for this item was present.

Validation: scompile.py compiled the complete module with no errors or warnings.
The only postponed declaration is finite_fibre_valuation_domination, with the nine
proof steps retained in its docstring. Delivery preflight and final compile are
run through deliver2.py.

## Second reading by Q140

The delivered second reading said it was the author's own second pass. This
section replaces it with an independent reading by the maintainer's reviewer.
The reviewer read the node, Temkin §4.2, the delivered module and the declarations
of every project dependency used: `HorizontalValuationBase`, `.T`, `.genericMap`,
`RelativeCurve`, `SchemeModification`, `SchematicallyDenseOpen` and
`IsCenteredValuation`. The Lean signature was unchanged.

Node statement as a list, with the Lean that renders it and a verdict:

1. K separably closed field, V ⊆ K valuation ring with fraction field K, primes
   of V a finite chain. Lean: `A : HorizontalValuationBase.{u}`, with fields
   `ValuationRing V`, `IsFractionRing V K`, `IsSepClosed K`,
   `Finite (PrimeSpectrum V)` and `primeChain`. Correct; the chain field is
   automatic for a valuation ring but harmless.
2. T = Spec V, η = Spec K. Lean: `A.T = Spec V`, and
   `A.genericMap = Spec.map (algebraMap V K)`. Correct.
3. C a T-curve: flat, finitely presented, pure relative dimension one, with no
   separatedness. Lean: `hcurve : RelativeCurve c`, which is flat, lfp, qc and qs,
   with `IsPureDimension 1` for every fibre. Correct.
4. C normal: every local ring is an integrally closed domain. Lean: `hnormal`,
   given inline for every stalk. Correct, and no integrality or nonemptiness of C
   is added.
5. Smooth generic fibre and finitely many components. Lean: `hsmooth` on
   `pullback.snd c A.genericMap`, and `hcomponents`. Correct.
6. q : W → C a modification with reduced source. Lean: `hq`, `hW`. Correct.
7. Centred valuation on a component C_i. Lean: `ComponentCenteredValuation C`.
   Its `generic` field is a generic point of a member of `irreducibleComponents C`,
   `ring` is a `ValuationSubring` of `C.residueField generic`, and `map` with
   `IsCenteredValuation` gives the specified generic-point morphism. The node takes
   L_i as the local ring at the generic point with the reduced structure. All the
   valuations quantified over live on the normal schemes C or B. There, that local
   ring is a reduced zero-dimensional local ring, so it is canonically the residue
   field. Correct. A `ValuationSubring` of a field has that field as its fraction
   field, as the node intends. The T-structure of ν is the composite with c.
8. Centre = image of the closed point. Lean: `ν.centre`. Correct.
9. Residual transcendence degree one, trdeg of κ(O) over κ(V_O), V_O = O ∩ K.
   Lean: `residualDegree c` = trdeg of κ(closed point of Spec O) over κ(s), where
   s is the image in T, through the induced residue map.
   - Check: by flatness the generic point of C_i lies over η, so K ⊆ L_i.
   - Since the closed point maps to s, V → O factors through a local map V_s → O.
     So O ∩ K is a valuation ring of K that dominates V_s.
   - Valuation rings are maximal for domination, so O ∩ K = V_s and κ(V_O) = κ(s).
   - The residue field of Spec O at its closed point is O/m_O.
   Correct, with no arbitrary field embedding.
10. There exists a finite set F, each member of residual degree one with a closed
    centre on C. Lean: `∃ F, F.Finite ∧ ∀ ν ∈ F, residualDegree = 1 ∧
    IsClosed {ν.centre}`. Correct.
11. Suppose p : C' → C is a modification, C' is normal, and the centre on C' of
    every ν ∈ F is fibre-generic. Lean: `SchemeModification p`, normal stalks, and
    `∃ l, l ≫ p = ν.map ∧ IsFibreGenericPoint (p ≫ c) (l closedPoint)`. A normal C'
    is reduced, so clause 2 makes the lift unique, and the existential is
    equivalent to a statement about the centre of the unique lift. Correct.
12. Then there is a unique C-morphism h : C' → W, and h is a modification. Lean:
    `∃ h, h ≫ q = p ∧ SchemeModification h ∧ ∀ h', h' ≫ q = p → h' = h`.
    Uniqueness is among all C-maps. Correct.
13. For every reduced-source modification, every centred valuation on C lifts
    uniquely. Lean: `∃! l, l ≫ p = ν.map` for every ν, with no degree or closedness
    restriction. Correct.
14. A closed original centre gives a lifted centre that is either fibre-generic or
    closed in C'. Lean: an implication from `IsClosed {ν.centre}` to the
    disjunction. Correct; the image in T is not required to be closed.
15. For B a normal T-curve with smooth generic fibre and r : B' → B a modification
    with reduced source, r is an isomorphism over a neighbourhood of every
    fibre-generic point. Lean: `∃ U ∋ x, IsIso (r ∣_ U)`. Correct. The node does not
    require finitely many components here, and the Lean does not either.
16. Consequently, valuations centred at such points keep fibre-generic centres on
    B'. Lean: for every ν on B and every lift l, fibre-generic `ν.centre` implies a
    fibre-generic lifted centre. Correct.
17. "Generic point of its T-fibre". Lean: `IsFibreGenericPoint c x`, meaning
    `c.asFiber x` is the generic point of an irreducible component of
    `c.fiber (c x)`. This is the fibre through x, not the generic fibre. Correct.

Edge cases:
- If W = C, an empty F serves.
- A trivial valuation O = L_i has a nonclosed centre at the component's generic
  point, so it is excluded from the dichotomy hypothesis only through
  closedness, as in the node.
- Empty fibres and an empty C are not excluded.
- All schemes are in one universe u, the universe of V and K. The C' and B, B'
  quantifiers range over `Scheme.{u}`, which is the node's generality.
- `residualDegree` is a `Cardinal.{u}`, compared with 1.

Searches:
- `IsCenteredValuation` is used only in CenteredValuation and
  BirationalQuasiModificationCommonCover.
- The existing `CenteredValuation` / `residualTrdeg` bundle in
  SingleValuationSemistableExtraction requires a `StrictSemistableCurve` and a
  closed centre, so it cannot serve here.
- The fibre-generic condition in FlatFibreGenericGeneralization and
  ValuationExceptionalClosedImageCriterion is inline or specialised to
  multipointed-curve maps.
- So the three helpers are not second definitions of an existing general notion.

Compile: nt_compile.py on the module compiled cleanly, with exit status 0 and no
warning besides `sorry`, in 4.6 s.

Mismatches found: none in the Lean or in the records. Only this section was changed.
