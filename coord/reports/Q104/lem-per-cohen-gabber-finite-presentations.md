## Worker report

The module `Sheaf.RingTheory.CohenGabberFinitePresentations` states
`IsLocalRing.cohen_gabber_finite_presentations`, with its only proof `sorry`.
It introduces no definition, helper, new node, dependency replacement, or statement
correction. The theorem docstring carries all ten proof steps of the node and their
mathematical inputs. I read ILO IV 2.1.1–2.1.12, IV 4.2.1–4.2.5, V 3.1.3–3.1.4,
and the statement of Stacks 032D in the available local sources.

Hypotheses and clauses:

- A complete Noetherian normal local domain: `(A : Type u) [CommRing A]`,
  `[IsLocalRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]`,
  and `[IsAdicComplete (maximalIdeal A) A]`.
- Dimension d≥2: `(d : ℕ) (hd : 2 ≤ d)` and
  `(hdim : ringKrullDim A = (d : WithBot ℕ∞))`.
- Separably closed residue field: `[IsSepClosed (ResidueField A)]`.
- The conclusion is the conjunction of the equal-characteristic assertion and the
  mixed-characteristic assertion. Equal characteristic is
  `ringChar A = ringChar (ResidueField A)`. Mixed characteristic (0,p) is
  `p.Prime`, `ringChar A = 0`, and `ringChar (ResidueField A) = p`.
  These exhaust the cases of a local domain: its characteristic is zero or prime;
  in prime characteristic its residue field has that same characteristic, while
  in characteristic zero the residue characteristic is zero or prime. Thus these
  conditional assertions also give the node's unconditional existence claim.
- In equal characteristic A'=A is implemented literally: `φ` has target `A`,
  and the finite injective map A→A' is the identity. No merely isomorphic substitute
  for A is introduced. The coefficient ring has `[Field Λ]`, and the power-series
  index is `Fin d`, implementing r=d. Input `hd` implies r≥1.
- In mixed characteristic A' is existential, with `CommRing`, `IsLocalRing`,
  `IsDomain`, and `IsIntegrallyClosed` structures. Its map `ι : A →+* A'`
  satisfies `Function.Injective ι ∧ ι.Finite`. The local-ring structure supplies
  exactly the structure needed by the node's local map into A' and its residue field.
- The mixed coefficient ring has `CommRing Λ`, `IsDomain Λ`,
  `IsDiscreteValuationRing Λ`, `IsAdicComplete (maximalIdeal Λ) Λ`, and
  `ringChar (ResidueField Λ) = p`. Its index is `Fin (d - 1)`, hence r=d−1;
  `hd` implies r≥1. No unramified/Cohen-ring restriction is placed on this DVR.
- In both cases `IsSepClosed (ResidueField Λ)` is asserted. In the field case
  the residue field is canonically Λ; this says exactly the coefficient clause.
- The map from R=Λ[[t_1,...,t_r]] is `φ : MvPowerSeries (Fin r) Λ →+* A'`,
  where r is d or d−1 as above. It has `IsLocalHom φ`, `Function.Injective φ`,
  and `φ.Finite`. `RingHom.Finite` is Mathlib's abbreviation using `φ.toAlgebra`
  for `Module.Finite`, so both finiteness clauses use the module notion of the node.
- `Function.Bijective (ResidueField.map φ)` is an isomorphism on residue fields
  induced by this exact map, rather than an unrelated isomorphism of the fields.
- The element `f` belongs to this R. Its nonzero reduction is the explicit condition
  `MvPowerSeries.map (residue Λ) f ≠ 0`, in the power-series ring over Λ/m_Λ.
  Étaleness is `(Localization.awayMap φ f).Etale`, the canonical map
  R[1/f]→A'[1/φ(f)]. The denominator is in the base, as the source requires.
- All 0≤j≤r: `∀ j : ℕ, j ≤ r → ...`. `IsRegularLocalRing` includes locality
  and Noetherianity by its parent classes. Completeness is separately the maximal-
  ideal-adic `IsAdicComplete` clause. `ringKrullDim` is j in the field case,
  and j+1 in the DVR case. The formula is asserted for the same coefficient ring
  used in the finite presentation, and includes j=r.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  normal-domain clause uses this together with `IsDomain`, as recorded inline.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (the node also records
  `IsSepClosure`, which this statement does not need).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, through `RingHom.Finite`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and its coefficient map.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` and its
  `HasRingHomProperty` correspondence with `RingHom.Etale`; the latter is used for
  the ring map, as authorized by the ÉTALE RING MAPS convention.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: the recorded module of
  `def-weil-regular-scheme`; the unchanged ring clause in its `mathlib_match` is
  `Mathlib.RingTheory.RegularLocalRing.Defs.IsRegularLocalRing` (global name
  `IsRegularLocalRing`). This statement needs that ring clause, not its scheme clause.

Additional Mathlib APIs: `IsLocalRing.ResidueField.map` is the induced residue map
for a local homomorphism; `Localization.awayMap` is its canonical localized ring
map. Their full signatures and docstrings were read. Definitions are reused, with
no data chosen from a postponed theorem.

The stated proof-dependency modules are imported non-publicly: power-series
quotient variables, complete over complete base, complete-local finite
normalization, integral dimension equality, complete power-series universal
property, and regular-principal-prime DVR localization. Mathlib proof leaves are
also imported. The following proof nodes have no Lean record or Mathlib match,
so there is no module to import yet: `lem-per-finite-algebra-etale-near-field-or-dvr`,
`lem-per-coefficient-field-generic-differential-basis`,
`lem-per-parameter-ideal-formal-normalization`,
`lem-per-finite-formal-map-differential-cokernel`,
`lem-per-mixed-reduced-special-fibre-cover`, and
`lem-per-perfect-residue-coefficient-dvr`. None is needed to type the statement.

Edge cases checked: j=0 yields the coefficient field (dimension 0) or the complete
DVR (dimension 1); j=r includes the full base. At d=2 the mixed case has one
variable, with no truncated-subtraction issue. The equal-characteristic branch
includes both zero and positive characteristic and uses A itself. Separably
closed imperfect fields are allowed; no perfect-field hypothesis was added.
The mixed DVR may be ramified. Nonzero reduction of f implies it is nonzero and
ensures the base open meets the special fibre. The zero ring is correctly excluded
by the domain hypothesis. All types and universes are explicit; witnesses may
live in A's universe because the coefficient ring is a subring up to equivalence
and the cover is finite. There is no independent, potentially vacuous test universe.

Searches for an existing statement (through msearch.py, group Q104, this item):

- LeanFinder query `Cohen Gabber finite generically etale power series subring
  complete normal local domain`: 8 hits, standard étale presentations, étale loci,
  and related smoothness facts; none is this theorem.
- Loogle query `"PowerSeries", "Etale"`: 0 hits.
- Mathlib grep query `Cohen.?Gabber|cohen.?gabber|genericallyEtale`: 0 hits.
- LeanSearch query `Cohen Gabber theorem complete local normal domain finite
  generically etale formal power series ring`: 8 hits, étale loci and formal
  étaleness properties; no Cohen–Gabber theorem.
- Direct rg of `Cohen.?Gabber|cohen.?gabber|lem-per-cohen-gabber-finite-presentations`
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
  `lean/Sheaf`: 0 hits. A separate rg of the proposed full declaration name in
  Mathlib, upstream, and side sources: 0 hits. The upstream name index also has
  no entry for this node. The nearby existing finite-normalization theorem lacks
  generic étaleness and the mixed-characteristic cover and is a proof input only.

Validation: scompile.py compiled the sandbox probe and final library module
cleanly, in 2.7 s and 2.5 s respectively. Every theorem proof is `sorry` as required.
No statement dispute or node fault was found.

## Second reading by Q104

I reopened the node and the final Lean source for a separate in-thread rereading;
the maintainer's independent review remains the external second reader prescribed
by the dispatch brief. No other agent was started.

The hypotheses agree one by one: local, complete, Noetherian, domain, integrally
closed, separably closed residue, dimension d, and d≥2. The two characteristic
conditions cover all cases of that domain. The equal case targets A literally,
uses a field and d variables; the mixed case gives the finite injective A→A',
normal local domain A', complete DVR of residue characteristic p, and d−1 variables.
Both assert the separably closed coefficient residue field, injective finite local
power-series map, and bijective induced residue map. The localized étale map
comes from the same φ, and coefficientwise reduction of the same f is nonzero.
The final universal clause includes every j, especially 0 and r, with regular
local (hence Noetherian local), complete, and the exact dimensional formula.
No hidden arbitrary-map choice, extra perfectness, unramified-DVR restriction,
or weakened special-fibre clause was found. No changes were needed on rereading.
