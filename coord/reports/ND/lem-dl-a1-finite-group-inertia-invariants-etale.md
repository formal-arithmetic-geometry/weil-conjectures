## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGroupInertiaInvariantsEtale` states
`AlgebraicGeometry.exists_etale_neighborhood_inertia_invariants`, with its entire
proof `sorry`. There are no new definitions or auxiliary theorems. The node changes
only in `lean`; its statement and dependency lists are unchanged.

Source read: `literature/stacks-project/pione.tex`, lines 2664–2782, Tag 0BST,
`lemma-inertia-invariants-etale`, including all four reduction paragraphs. The node
states exactly that lemma, expressing etaleness at the prime by an open neighbourhood
in the source spectrum. The six-step node proof is included in the declaration's
docstring, including the finite Boolean refinement and the final source-cover descent.

Hypotheses and objects, matched individually:

- A finite group is `(G : Type v) [Group G] [Finite G]`. No enumeration or faithful
  action is required.
- A commutative ring is `(R : Type u) [CommRing R]`. The independent universe `v`
  for the group imposes no restriction on the universe `u` of the ring.
- An action by ring automorphisms is `[MulSemiringAction G R]`. A group semiring
  action preserves addition, multiplication, zero and one, and its inverse action
  supplies the inverse ring homomorphism.
- The chosen prime ideal is `(q : PrimeSpectrum R)`; its ideal is `q.asIdeal`,
  with primality carried by `q.isPrime`. This bundles precisely the prime hypothesis.
- The full invariant subring is the existing `FixedPoints.subring R G`, whose
  membership is definitionally `∀ g : G, g • r = r`.
- The inertia group is the existing `q.asIdeal.inertia G` (the inherited
  `AddSubgroup.inertia`), with membership `∀ r : R, g • r - r ∈ q.asIdeal`.
  This equals the node's definition: the condition implies that g acts identically
  on R/q. It also implies preservation of q, since r in q gives g(r) in q and the
  inverse group element gives the reverse inclusion. The quotient is a domain, so
  its identity action extends to its fraction field. Conversely, identity on the
  fraction field implies identity on the embedded quotient and hence the difference
  condition. The source's prime-preservation and residue-field clauses are both
  retained, with no separability or maximality condition.
- The inertia invariant subring is `FixedPoints.subring R (q.asIdeal.inertia G)`.
- The contracted prime `q_I` is
  `PrimeSpectrum.comap (FixedPoints.subring R (q.asIdeal.inertia G)).subtype q`.
  By the definition of comap its ideal is the inverse image along the actual inclusion
  of that subring into R, exactly the intersection in the node.

Conclusion, matched clause by clause:

- The morphism from Spec(R^I) to Spec(R^G) is `Spec.map (CommRingCat.ofHom ...)`.
  Its ring homomorphism is Mathlib's `Subring.inclusion`, with the inclusion witness
  `fun (x : R) (hx : x ∈ FixedPoints.subring R G)
    (g : q.asIdeal.inertia G) ↦ hx g.1`.
  Its value is literally x; there is no arbitrary map or comparison choice.
- The open neighbourhood is `∃ U : (Spec (.of (FixedPoints.subring R
  (q.asIdeal.inertia G)))).Opens`. The first conjunct says the contracted prime belongs
  to U, so it is a neighbourhood of the required source point.
- `Etale (U.ι ≫ Spec.map ...)` is the second conjunct. This restricts the displayed
  morphism to U in its source, exactly as required; no neighbourhood in the target
  is demanded and global etaleness is not asserted.
- The absence of Noetherian, module-finiteness and invertibility hypotheses is literal:
  no such binders occur. There is also no domain, reducedness, maximality or
  characteristic restriction on R.

Recorded statement dependencies used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`. Read their definitions
  and docstrings at lines 470–480.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`. Read its class at lines 37–44 and the equivalence with
  flat, formally unramified, locally finitely presented at lines 140–144.

Other existing constructions read and used: `FixedPoints.subring` in
`Mathlib.Algebra.Algebra.Subalgebra.Operations:98`, `AddSubgroup.inertia` and
`AddSubgroup.mem_inertia` in `Mathlib.Algebra.Group.Subgroup.Basic:1166,1174`,
`Ideal.inertia_le_stabilizer` in `Mathlib.RingTheory.Ideal.Pointwise:175`,
`Subring.inclusion` in `Mathlib.Algebra.Ring.Subring.Basic:901`, and
`PrimeSpectrum.comap` in `Mathlib.RingTheory.Spectrum.Prime.RingHom:35`.
Read `IsFractionRing.ker_stabilizerHom` in `Mathlib.RingTheory.Invariant.Basic:324`
as a further check of the agreement of Mathlib's inertia with the residue kernel.

Proof imports cover the already stated proof dependencies: invariant integrality,
prime orbits and residue normality (`Mathlib.RingTheory.Invariant.Basic` and
`.Galois`); tensor products (`Mathlib.LinearAlgebra.TensorProduct.Map`);
etale permanence and base change (`Mathlib.AlgebraicGeometry.Morphisms.Etale`);
integral closed maps and clopen idempotents (`Mathlib.RingTheory.Spectrum.Prime.Topology`,
provided transitively); finite affine coproducts (`Mathlib.AlgebraicGeometry.Limits`);
open images (`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`); and
`AlgebraicGeometry.Etale.of_comp_of_surjective_etale` in
`Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover` (signature and docstring read).
The integral-normal-residue splitting and flat-invariant-base-change proof nodes
have no recorded Lean declarations in the read repository, so they supply no imports.
They are not statement prerequisites of this item.

Edge cases checked mathematically before writing:

- Trivial G, or any trivial/nonfaithful action: both invariant rings are R, the map
  is the identity, and the whole spectrum is a suitable neighbourhood.
- I = G: the two invariant rings coincide and the same identity case applies.
- I trivial: the conclusion concerns R over R^G at q, retaining wild and modular
  actions when the inertia at the chosen prime is trivial.
- Positive characteristic dividing the group order: the statement has no division
  by the order and permits this case, as does Stacks 0BST.
- Arbitrary prime, including a nonmaximal prime: the inertia difference criterion
  uses Frac(R/q), not an unjustified field structure on R/q.
- The zero ring: there is no q : PrimeSpectrum R, so no point is spuriously required
  to have a neighbourhood. No explicit Nontrivial hypothesis is added.
- No finite-module or Noetherian condition is used to express etaleness; an open
  source neighbourhood is the conclusion itself.

Searches run on 2026-10-21 (all via the prescribed msearch wrapper where named):

- LeanFinder: "For a finite group acting on a commutative ring the fixed ring of the
  inertia subgroup is etale at the contracted prime". Eight hits, including
  `Algebra.IsEtaleAt`, Frobenius elements and inertia degrees; no exact theorem.
- Loogle: `Algebra.Etale, FixedPoints.subring`. Zero hits.
- LeanSearch: "For a finite group acting on a ring the inertia invariant ring is etale
  over the invariant ring near the contracted prime". Eight hits, including
  `Algebra.IsInvariant.isIntegral`, `AddSubgroup.inertia` and
  `Ideal.inertia_le_stabilizer`; no exact theorem. These identified the usable inertia
  construction, which the module reuses.
- msearch grep: `inertia.*[Ee]tale|[Ee]tale.*inertia|inertiaInvariants`. Zero hits.
- Direct rg searches in Mathlib found the fixed-subring definition, inertia subgroup,
  prime contraction and canonical inclusion at the source locations listed above.
- Direct rg searches of `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the item id, inertia/etale combinations and the
  proposed full declaration name found no exact existing statement and no name clash.
  The upstream `Ideal.exists_etale_localization_away_of_inertia` in
  `WeilConjectures.RingTheory.InertiaUnramifiedPoint` was read: it assumes a Dedekind
  base, perfect residue field and a finite etale generic algebra, so does not state
  the present arbitrary-ring theorem. The upstream inertia-invariant ind-etale
  statements concern a localized integral closure and are also different.

Validation: the prescribed scompile.py succeeded for this file both as
`Sheaf.Stage2.Sandbox0` (1.9 s) and as its final module name (1.8 s), with no errors
or warnings. There are no statement faults or STATEMENT-DISPUTED issues.

## Second reading by ND

This is the dispatcher's single-worker delivery; no separate worker or independent
review is claimed. I reread the node, Stacks 0BST and the finished signature after
compilation. The group's second pass checks the correspondence above: G is finite;
R is arbitrary and commutative; the action is by automorphisms; q is any prime;
Mathlib's inertia is exactly the prime stabilizer's residue kernel; both fixed rings
are the genuine Mathlib subrings; the map is their canonical inclusion; the point is
its contraction from q; and the existential open lies in the source spectrum with
that point as a member. The second conjunct asserts etaleness of the restricted map.
No hypothesis or conclusion changed, and no mismatch was found. The independent
mathematical review is the maintainer's review of this delivery, as specified in the
brief. No other agent was started.
