## Worker report

The delivery states `AlgebraicGeometry.VeryTameLocalKummer.invariant_chart_and_stratum`
and `AlgebraicGeometry.VeryTameLocalKummer.invariant_chart_on_pointed_etale_neighbourhood`
in `Sheaf.AlgebraicGeometry.VeryTameLocalKummerQuotient`. Both proofs are `sorry`.
The two theorems together state all clauses of the unchanged DAG statement. The
remaining declarations give real data: the affine fs log scheme and explicit canonical
fixed ring, character kernel, inverse-image submonoid, structural chart map and chart
ideal. `Data` and `StalkData` package this node's hypotheses, not alternative log
structures or alternative quotient notions. No definitions contain postponed data.
No new DAG nodes or dependency repairs are needed.

I read the full node, all six statement dependencies and their recorded Lean declarations,
and ILO Exposé VI 3.4, 3.5(b), and 3.7(b)--(c), printed pp.74--76, directly from the
local PDF (PDF pages 80--82). The existing example `CompactObject.lean` is withdrawn;
I also read its current upstream replacement `WeilConjectures.CategoryTheory.CompactObject`.
There was no repair note for this item. Its historical reviewed_lean note records a
withdrawn earlier interface; no current declaration of the item was found.

Hypothesis correspondence for the strictly local theorem:

- The binders `[CommRing A] [IsNoetherianRing A] [IsStrictlyHenselianLocalRing A]`
  are precisely the Noetherian strictly henselian local ring. `affineLogScheme A M hM`
  has scheme exactly `Spec (.of A)` and the specified `M`, with its genuine fs proof.
- `Data.logStructure`, `fs`, `a`, `chart`, `fineSaturated`, `sharp` give the fs log
  structure and sharp fs chart. The monoids use multiplicative notation: their
  additive zero is `1`. Fine saturation of Q is inherent in the characteristic of
  an fs log structure. `point`, `closed` specify a closed geometric point, and
  `characteristic` says the map induced by the prescribed chart to its characteristic
  is bijective. This tests the actual geometric log stalk and its Associates quotient.
- `[Group H] [Finite H]`, `action` give the finite log action. `σ` is its coordinate-ring
  pullback: `ringAction` pins it to the action through `Scheme.ΓSpecIso`, so it is not
  a free auxiliary action. The pullback convention is contravariant; no incorrect
  same-order ring-action law is imposed. `residue` says this action on A/m is trivial.
- `orderUnit` is invertibility of n = Nat.card H. `root`, `primitive`, `rootFixed`
  specify the H-fixed primitive n-th root. No positive characteristic is assumed.
- `χ : GrothendieckGroup Q →* (H →* rootsOfUnity n A)` is the curried character
  pairing. Homomorphisms from H to this abelian group factor through H_ab;
  homomorphy in the group-completed monoid is the tensor pairing's other variable.
- `diagonal` is the log-section identity h(a(q)) = chi_q(h)*a(q), including an
  actual log unit whose structural image is the stated root. The unit condition
  determines this log unit uniquely. It is not merely the weaker ring identity,
  which would lose information when monomials vanish or are zero divisors.
- `chartRingMap M a` uses the prescribed structure map and ΓSpecIso, not a new
  chart. `chartIdeal` is the ideal of its nonidentity monomials, exactly I.
  `stratum` says σ(h)(r)-r lies in I, exactly triviality on A/I.
- `fixedRing σ` is the intersection of Mathlib's equalizer subrings
  `RingHom.eqLocus (σ h).toRingHom (RingHom.id A)`, exactly B=A^H.
  `finite` is Module.Finite B A for the canonical subring algebra structure.

Conclusion correspondence:

- `lattice χ` is χ.ker. Since equality of homomorphisms to the character group is
  pointwise equality, this is exactly all group-completed q with chi_q(h)=1 for all h.
  `invariantMonoid χ` is its inverse image in Q under the canonical group-completion
  map; integrality of Q identifies it with L intersect Q, without choosing an embedding.
- The first two conjuncts are fine saturation and sharpness of P. The `mrange`
  equality is P^gp=L inside Q^gp, using the canonical lift of the inclusion P→Q.
  The fs/integrality conclusions ensure that this canonical group map is injective.
  The next conjunct is L.FiniteIndex; the next says g^n belongs to L for every g,
  which is n Q^gp contained in L in the node's additive notation.
- The existential b has codomain B, and its displayed equality after the subring
  inclusion forces b(p)=a(p) for every p in P. This is the prescribed chart map,
  not an arbitrary map into B. `chartIdeal b` is exactly J.
- The ring equivalence e : B/J ≃+* A/I is pinned on every representative to the
  subring inclusion followed by quotient. It therefore says the NATURAL map is
  an isomorphism, not merely that the quotient rings happen to be isomorphic.
- The final existential supplies N and the dependency's genuine
  `action.InvariantDirectImage f N`, where f is exactly Spec of B↪A. This interface
  identifies every sheaf of sections with actual invariant sections and preserves
  the structural maps; it does not assume N fs in advance.
- `N.IsChart` is tested at every geometric point. `chartRingMap N c = b` identifies
  the chart with that exact b. Its pullback is the restriction of the original
  log chart a to P, compared through the canonical pullback test object. The map j
  quantified there is the unique inverse of pullback.snd for the identity target
  test, so this comparison is not vacuous. The final bijectivity statement
  identifies P with the characteristic at the image of the specified closed point.
  A global chart on the strictly local Spec B is equivalent to a chart near its
  closed point: every open neighbourhood of that closed point is the whole scheme;
  a pointed étale neighbourhood has a section through it by strict henselianity.

Original-quotient neighbourhood clause:

- The second theorem takes an arbitrary original finite group G, its fs log scheme
  X, and `IsAdmissibleFiniteSchemeQuotient action.baseAction f`. The original
  quotient need not be affine or strictly local. It uses a subgroup H with the
  explicitly stated geometric-stabilizer property; `inertia` is required to agree
  with the original log action on H. This includes nontrivial orbits and H≠G.
- `StalkData` is exactly the same specified local data in the original ring
  `strictLocalRing X t` and log stalk. `pullback` pins both σ and τ to pullback
  on every pointed relative test. Its localRing field is the intrinsic local-ring
  structure of the strict local ring (a Prop, not an additional restriction).
  `chart`, `characteristic`, fs/sharpness, the fixed primitive root, residue and
  stratum conditions, and module finiteness are the original local hypotheses.
- The conclusion constructs the actual invariant log sheaf via `InvariantDirectImage`
  and an object `W : Y.Etale` with `w` over the original quotient point.
  `N.IsChart W b` is the chart on this pointed étale neighbourhood. Its characteristic
  map is bijective, and its germ pulled back to the original source point is
  exactly `d.a` restricted to P. The lift z is the canonical pointed lift to the
  fibre product (it exists by the pullback universal property). Thus the clause
  retains the specified chart germ and does not merely produce an unrelated chart.
- Neither theorem assumes regularity of A/I, a logarithmic dimension formula,
  generic freeness, or faithfulness of the action.

Dependencies used, with interfaces read in full:

- `def-trf-fs-log-blowup`: `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`,
  `EtaleLogStructure`, `FineSaturatedLogScheme`, `EtaleLogHom.sectionMap`,
  `EtaleLogStructure.IsChart`, `IsStalkChart`, `unitsIn`, and its geometric-stalk
  and characteristic constructions. The inherited
  `Sheaf.AlgebraicGeometry.LogRegularPair` gives `IsFineSaturatedMonoid`,
  `strictLocalRing`, and `strictLocalGerm` (used without private replacements).
- `def-weil-pbc-henselian-terminology`:
  `WeilConjectures.Mathlib.RingTheory.Henselian.IsStrictlyHenselianLocalRing`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`,
  through the Noetherian geometry import needed to assemble the affine fs log scheme.
- `def-weil-pbc-geometric-stalks`: `Sheaf.AlgebraicGeometry.PointedEtaleStalk`,
  the actual pointed-neighbourhood monoid colimit used by the existing log structures;
  `Scheme.pointSmallEtale`, `Over.homMk`, and the prescribed germ maps represent points.
- `def-per-fs-log-group-action`: `Sheaf.AlgebraicGeometry.FSLogGroupAction`,
  `FSLogGroupAction`, `FSLogGroupAction.InvariantDirectImage`, and `logInvariantTest`.
- `def-per-admissible-finite-scheme-quotient`:
  `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient.IsAdmissibleFiniteSchemeQuotient`.
- The proof dependencies `lem-per-finite-quotient-strict-local-invariants`,
  `lem-per-tame-admissible-scheme-quotient`, and
  `lem-per-tame-diagonal-standard-closed-immersion` have no Lean records in the
  current DAG. Their modules cannot yet be imported; their proof steps are retained
  verbatim in meaning in the two theorem docstrings. They are not statement
  prerequisites, so no extraneous theorem modules are introduced in this delivery.

Searches (all prescribed msearch calls were for group Q32 and this item):

- LeanSearch: "Invariant log structure of a tame diagonal finite group action has an
  invariant monoid chart and the same logarithmic closed stratum". Eight hits include
  `Algebra.IsInvariant.isIntegral`, `Algebra.IsInvariant`, `Representation.diagonal`,
  and ordinary fixed-point/topological actions; none states logarithmic chart descent.
- LeanFinder: "Invariant logarithmic chart of a diagonal tame finite group action and
  quotient stratum ring isomorphism". Eight hits include finite Galois-category
  quotients, `Ideal.Quotient.stabilizerHom`, and number-field unit logarithms; no match.
- Loogle: `"IsPrimitiveRoot"` found Mathlib's existing primitive-root predicate and
  its lemmas, used here. No new root-of-unity predicate was defined.
- Mathlib grep via msearch: `LogStructure|localKummer|invariantLog`, restricted to
  AlgebraicGeometry, gave zero hits. Direct rg found and read existing equalizer
  subrings, GrothendieckGroup.of/lift, rootsOfUnity, and primitive roots.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `veryTameLocal`, `kummerQuotient`, and `KummerQuotient` found only a proof-docstring
  reference in RigidifiedQuotientTowerComparison; no theorem for the item.
  The explicitly prescribed grep of the item id in WeilConjectures gave no match.
  A name check in dag/lean_names_upstream.json and both source roots found no
  `VeryTameLocalKummer` namespace or conflicting theorem names.
- `scompile.py --source Sheaf.AlgebraicGeometry.VeryTameLocalKummerQuotient` confirmed
  this proposed module was not already available on the live server.

Edge cases checked before finalization: Q={1} makes I=J=0; trivial stratum action
then fixes all of A, so B=A. H={1} has n=1, root 1, L=Q^gp and P=Q. Trivial pairing
and nonfaithful actions are allowed. The sign action on Q=N has P=2N; the diagonal
sign action on N² has P generated by (2,0),(1,1),(0,2), so the statement does not
silently assume P is free. Nonunits with zero or nilpotent structural images remain
valid because the eigenidentity is in log sections. Positive characteristic is
allowed exactly when n is invertible. The empty scheme/zero ring has no closed
geometric point and is already excluded by the stated strictly local hypothesis.
The original-quotient theorem explicitly allows a larger G with proper inertia H.
All universes are explicit; the group universe v is independent of scheme/monoid u.

Validation: the prescribed scompile.py compiled this module in sandbox and library
module modes cleanly (11.5 s and 9.5 s on the final code). No warning remains, no
#check probe remains, and all lines have at most 100 characters. The node is copied
with only lean changed; there is no statement correction or disputed statement.

## Second reading by Q32

Author's separate second pass, with node and Lean source reopened; the independent
maintainer review remains the delivery's external review. No other agents were started,
as explicitly required by the dispatcher brief.

I checked every hypothesis and conclusion against the correspondence above. The first
pass had a 114-character line in the log eigenidentity; it was wrapped and the clean
compile repeated. The neighbourhood assertion was checked to include an original
larger group G and proper inertia H, not only the all-fixed case. The natural B/J→A/I
map is pinned on representatives; the log chart is pinned both structurally to b and
on source pullback to a|P. The invariant target is not assumed fs. The fixed-point
argument retains the unit twist. P^gp is the range of the actual canonical completion
map, with injectivity supplied by the fs conclusions. No regularity, dimension, or
free-monoid hypothesis was introduced. I found no remaining mismatch with the node.
