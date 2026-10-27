## Worker report

The module `Sheaf.RingTheory.IndEtaleResidueActionRigidity` states
`Algebra.indEtale_residue_action_rigidity`, with one `sorry` and no new definitions.
The node's statement, dependency lists and proof are unchanged. No statement fault
or disputed claim was found. All variables and universes are explicitly bound;
`autoImplicit` is disabled.

Hypothesis and object correspondence:

- The commutative local base H is `(H : Type u) [CommRing H] [IsLocalRing H]`.
  Its residue field κ is `IsLocalRing.ResidueField H`.
- The local H-algebra R is `(R : Type v) [CommRing R] [IsLocalRing R]
  [Algebra H R]`. Its ind-etale hypothesis is
  `hR : RingHom.IndEtaleAcrossUniverses (algebraMap H R)`, using the dependency's
  existing canonical ULift transport, rather than equating the ring universes.
- The chosen separable closure κs is `ResidueField R`, with
  `[IsSepClosure (ResidueField H) (ResidueField R)]`. This is the node's residue
  field of R, identified with its chosen closure. Taking the actual residue
  quotient as the representative loses no choice of separable closure: a named
  closure with a residue identification transports to this formulation, and
  conversely the identity supplies the identification. No special field model
  such as `SeparableClosure κ` is imposed.
- The henselian local H-algebra T is `(T : Type w) [CommRing T]
  [HenselianLocalRing T] [Algebra H T]`; henselianity already includes locality.
  E is the actual `ResidueField T`.
- Both structural maps are local by `[IsLocalHom (algebraMap H R)]` and
  `[IsLocalHom (algebraMap H T)]`. Mathlib consequently supplies the canonical
  residue κ-algebra structures. Algebraicity of E/κ is
  `[Algebra.IsAlgebraic (ResidueField H) (ResidueField T)]`.
- The injective local H-map is `(i : R →ₐ[H] T) [IsLocalHom i]
  (hi : Function.Injective i)`. Its induced κ-embedding j is exactly
  `ResidueField.mapAlgHom' i`, not an independently quantified map. Its domain
  is a field, so its injectivity is automatic. Its reduction formula is the
  existing `ResidueField.mapAlgHom'_residue`.
- The arbitrary group and its H-algebra action are `(Γ : Type g) [Group Γ]`
  and `(ρ : Γ →* (T ≃ₐ[H] T))`. No faithfulness or finiteness is assumed.

Conclusion correspondence, in displayed order:

- `IsPurelyInseparable (ResidueField.mapAlgHom' i).fieldRange (ResidueField T)`
  states that E is purely inseparable over j(κs), using Mathlib's actual
  intermediate-field image and its canonical inclusion algebra structure.
- For every natural prime p with `ringChar (ResidueField H) = p`, every
  `x : ResidueField T` has an `n : ℕ` such that
  `x ^ (p ^ n) ∈ Set.range (ResidueField.mapAlgHom' i)`. This is exactly the
  positive-characteristic clause, including n = 0.
- When `ringChar (ResidueField H) = 0`,
  `Function.Surjective (ResidueField.mapAlgHom' i)` states E = j(κs).
- `Set.MapsTo (ResidueField.mapAlgEquiv' (ρ γ)) (Set.range j) (Set.range j)`
  states preservation of j(κs) for each γ. Since this also holds for γ⁻¹, it
  is preservation onto the subfield, rather than just one inclusion.
- `∃ r : Γ →* (ResidueField R ≃ₐ[ResidueField H] ResidueField R)` states
  existence of the restriction group homomorphism into Gal(κs/κ). The clause
  `j (r γ x) = ResidueField.mapAlgEquiv' (ρ γ) (j x)` specifies its value on
  every element. Injectivity of j uniquely determines r, so this existential
  is the actual restriction, with no arbitrary homomorphism substituted.
- For every γ, `(r γ = 1 ↔ ResidueField.mapAlgEquiv' (ρ γ) = 1)` gives the
  first equivalence, and
  `(ResidueField.mapAlgEquiv' (ρ γ) = 1 ↔ ∀ x : R, ρ γ (i x) = i x)` gives
  the second. Equality to the identity algebra equivalence is pointwise
  identity on E. Thus these are precisely the three conditions in the node.
- The final sentence about reduction uses the existing canonical
  `ResidueField.mapAlgEquiv'`, whose formula on residue representatives is
  `ResidueField.mapAlgEquiv'_residue`. No separate action on E is assumed.

Dependency declarations read and used:

- `Sheaf.RingTheory.IndEtaleUniverseTransport`:
  `RingHom.IndEtaleAcrossUniverses`, defined by the actual upstream
  `RingHom.IndEtale` on the canonical common-universe ULift map. Its public
  imports expose `Algebra.IndEtale`, whose data are a filtered colimit
  presentation with etale stages.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem`, and its imported Mathlib
  `IsSepClosure`. The former confirms the finite separable subextension
  interpretation of the separable-closure dependency; the latter is the
  closure hypothesis actually used in this statement.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the dependency's
  `HenselianLocalRing` is imported from Mathlib. Its extra
  `IsStrictlyHenselianLocalRing` is not imposed: R need not be henselian,
  and T need not have separably closed residue.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`:
  `ResidueField.mapAlgHom'`, `ResidueField.mapAlgEquiv'`, their residue formulas,
  and the canonical residue-field algebra instances.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`: the conclusion uses
  `IsPurelyInseparable`. The proof dependency's Mathlib match is
  `separableClosure.isPurelyInseparable`; its signature and docstring were read.
- `Mathlib.FieldTheory.Separable`: proof dependency `Algebra.IsSeparable`.
- `Mathlib.FieldTheory.IsSepClosed`: proof dependency `IsSepClosed`/`IsSepClosure`.
- `WeilConjectures.RingTheory.MapIntoHenselianColimit`: proof dependency
  `Algebra.map_into_henselian_colimit`, including its full prime, compatibility
  and unique-lift signature. These proof modules are imported without `public`
  except PurelyInseparable.Basic, whose predicate occurs in the statement.

The theorem docstring gives all six DAG proof steps: canonical reduction;
identification of the separable subfield with j(κs); preservation and restriction
with its group law; purely inseparable kernel rigidity; henselian uniqueness
for i and γ∘i; and the converse by residue representatives. Source text read:
Stacks `pione.tex`, lemma-identify-inertia (0BSW); `algebra.tex`,
lemma-map-into-henselian-colimit (08HR); `fields.tex`, lemma-separable-first
(030K). No correction of the source or node was necessary.

Edge cases checked before writing:

- Characteristic zero gives surjectivity of j, not a vacuous p-power clause.
- In characteristic p the exponent n may be zero; a nontrivial purely
  inseparable extension is allowed. No perfectness or finite-degree condition
  was added on E.
- A trivial group and a nonfaithful action satisfy the same universal statement.
- T may have nilpotents. For example, with H = R = k separably closed and
  T = k[ε]/ε², automorphisms can move ε while acting trivially on E = k and
  fixing i(R); the conclusion correctly concerns i(R), not all of T.
- The given i may be the identity and E = κs. No proper extension is required.
- Nontrivial Frobenius on an algebraic closure of a finite field moves its
  residue elements; for H = Fp and R = T = Fp-bar all three kernel conditions
  are simultaneously false for that element, as required.
- Local rings here have a genuine residue field; the zero ring is already
  excluded by the local-ring hypotheses in the source. No domain or reducedness
  assumption was imposed on H, R or T.
- Four independent universes u, v, w and g cover all ring and group sizes;
  the existing across-universes ind-etale predicate avoids an extra size equality.

Searches for an existing statement (all via the prescribed tools or direct rg):

- LeanFinder: "Automorphisms of a henselian local ring fix an ind etale subalgebra
  with separable closure residue field if and only if they act trivially on its
  algebraic residue field extension". Eight hits, including
  `IsLocalRing.ResidueField.mapAut`, `mapAut_apply`, etale factorization and
  formally unramified residue results; none states the full rigidity theorem.
- Loogle: `IsLocalRing.ResidueField.mapAut, AlgEquiv`: zero hits.
- Mathlib grep through msearch, scope RingTheory:
  `[Ii]nd[Ee]tale.*([Aa]ut|[Rr]esidue)|[Hh]enseli.*[Aa]ut|[Aa]ut.*[Hh]enseli`:
  zero hits.
- LeanSearch: "An automorphism of a henselian local ring fixes an ind etale local
  subalgebra with separable closure residue field if and only if it is trivial
  on the residue field". Eight hits: valuation inertia, HenselianLocalRing,
  its TFAE, residue map/mapAut and henselian instances or recursors; no match.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `ind.*[Ee]tale.*[Rr]esidue|residue.*[Rr]igidity|[Hh]enseli.*[Aa]ut|[Aa]ut.*[Hh]enseli`:
  related strict-henselization lifts, weak-etale results and the larger global
  inertia comparison. They do not state this general local-algebra theorem.
- Direct rg of the item ID in `lean/WeilConjectures`: no hit.
- Direct rg for the proposed declaration name and `residue_action_rigidity`
  in Mathlib, upstream, Sheaf and `dag/lean_names_upstream.json`: no hit.

Validation: both the initial statement and the final version (including Mathlib's
pure-inseparability predicate) compiled without warnings through scompile.py,
in both sandbox and library-module modes. The final library-mode compile took
6.2 seconds, below the unchanged 60-second limit. Delivery preflight follows.

## Second reading by Q90

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
