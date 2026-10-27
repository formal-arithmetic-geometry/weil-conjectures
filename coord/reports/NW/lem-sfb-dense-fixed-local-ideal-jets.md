## Worker report

The module Sheaf.AlgebraicGeometry.DenseFixedLocalIdealJets states
AlgebraicGeometry.DenseFixedJets.dense_fixed_local_ideal_jets, with its only proof
`sorry`. No definitions, axioms, or helper theorems are introduced. The node is unchanged
apart from lean and three added definition-node statement dependencies. Two already
landed nodes give algebra coactions and the canonical coordinate Hopf instance; the new
existing:true ownership node records the seven unchanged general local-jet helpers.

Source read: Milne, Algebraic Groups (2017), printed pp.9--10, Propositions 1.10 and
1.13; pp.86--87, Section 4(d); pp.255--256, Lemma 13.4 and proof of Lemma 13.6.
The affine-coordinate formulation follows the node's accepted proof, including its
extension of the local-ideal and jet argument to nonsmooth X. In Section 4(d), use the
right action z.g=g^{-1}z, so evaluation of the coaction is exactly inverse pullback.
This changes neither the given action data nor its identity/associativity laws.

Hypothesis-by-hypothesis correspondence:

- Algebraically closed k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Smooth affine finite-type k-group scheme: `G : Scheme.{u}`, `G.Over (Spec (.of k))`,
  `GrpObj (G.asOver (Spec (.of k)))`, `IsAffine G`, `Smooth` of the structure map,
  and `LocallyOfFiniteType` plus `QuasiCompact` of that map. These are precisely the
  dependency interfaces, with finite type their recorded conjunction.
- Affine finite-type X: `B : Type u`, `CommRing B`, `Algebra k B`, `Algebra.FiniteType k B`
  writes X=Spec B. This covers every affine finite-type scheme by its global sections.
- Algebraic action: `rho : HopfAction.AlgebraCoaction k (Gamma(G, top)) B`; its counit
  and coassociativity fields are the affine duals of identity and associativity.
  The Hopf structure is the canonical one of G, not an arbitrary additional structure.
- Abstract subgroup Gamma of G(k): `H : Subgroup (WithConv (Gamma(G, top) →ₐ[k] k))`.
  Mathlib's convolution multiplication is induced by the coordinate comultiplication;
  inversion is precomposition with the coordinate antipode. Thus these are G's actual
  k-points with their group law. `hdense : DenseRange (fun gamma : H => pointPrime
  gamma.val.ofConv)` is topological Zariski density on Spec k[G], canonically |G|.
- Closed immersion F into X: `K : Ideal B` represents F=Spec(B/K). Every closed
  immersion into affine X is of this form, including nonreduced F. The hypothesis
  `hfixed` says for every commutative k-algebra D and q:B→D that K is killed iff
  every gamma's evaluated coaction fixes q. Inverse elements give exactly the same
  fixed-point condition as the original left action.
- Point x in F(k): `x : (B ⧸ K) →ₐ[k] k`; its image in X is `quotientPoint K x`.
  All test algebras live in Type u, including coordinate and quotient algebras; this
  is the universe convention of the existing affine point/coaction interfaces and
  includes their universal points. It imposes no dimension, characteristic, or
  cardinal restriction on the given data.

Clause-by-clause correspondence:

- Scheme-theoretic G-fixedness: the first conjunct quantifies every D and every
  g:k[G]→D and equates evaluated rho at the scalar-extended point with that point.
  No reduction of D or restriction to field-valued points occurs. Inversion permutes
  all g, so fixedness for the right inverse action is exactly the asserted left fixedness.
- A=O_{X,x}: `TorusFixedJets.LocalRing (quotientPoint K x)` is literally
  Localization.AtPrime of the rational-point kernel. The maximal ideal is Mathlib's
  `IsLocalRing.maximalIdeal`. The displayed residue AlgEquiv with k is normalized
  on B by x, so it gives the stipulated residue field, not an arbitrary identification.
- gamma*: the witness tau:H→(A≃ₐ[k]A) is pinned on every b in B to evaluation of
  rho at gamma; localization makes this the unique induced automorphism of A.
- J: the existential ideal is equated to `Ideal.span` of tau gamma f-f, for every
  gamma:H and f in the actual maximal ideal. This is a determined ideal, not arbitrary data.
- O_{F,x}=A/J: the displayed k-algebra equivalence from A/J to LocalRing x is
  pinned on every b to the quotient B→B/K followed by localization. Hence it is
  exactly the immersion-induced comparison. An algebra equivalence between local
  rings is automatically local; no unrelated local-algebra structure is chosen.
- For all n≥1: the family c contains algebra coactions on `Jet ... N`, which is
  literally A/m^N; the quantified clause uses N=n+1 and states `FiniteDimensional k`.
  AlgebraCoaction includes exactly the algebra map, counit, and coassociativity.
- Evaluation at gamma: the next conjunct states evaluation of c on jetMap(a) equals
  jetMap(tau gamma a), for all a:A and gamma:H. This pins each coaction on a dense
  set and therefore identifies the induced algebraic action, not a trivial substitute.
- M_n=m/m^{n+1}: `JetIdeal ... (n+1)` is the image of m in A/m^{n+1}, with its
  actual inclusion. A linear coaction d satisfies both laws and commutes with this
  inclusion. Over k, inclusion tensor k[G] is injective, so this is the specified
  rational subrepresentation.
- V=m/m^2: d₂ has the same two laws and is the restriction of c 2 along the actual
  inclusion of `JetIdeal ... 2`.
- Natural quotient q_n: p is pinned on every representative a:m to its class modulo
  m², explicitly surjective, and satisfies the tensor intertwining equation
  `p.rTensor k[G] ∘ₗ d = d₂ ∘ₗ p`. This is exactly G-equivariance.
- Rational representation is the linear coaction notion of the node. The imported
  RationalRepresentationComoduleDictionary also states its equivalence with natural
  actions on R tensor V and, in finite dimension, group-scheme maps to GL(V).
  Tensor symmetry identifies that convention with V tensor R. No extra equivalence
  theorem is restated here.
- No smoothness/regularity of B or X, and no linear reductivity, connectedness or
  irreducibility hypothesis appears.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed
  (the recorded algebraic-closure dependency explicitly includes this notion).
- Mathlib.CategoryTheory.Monoidal.Grp: GrpObj, with its multiplication, identity,
  inverse and diagrams; read also WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom, Spec; the affine presentation
  uses Mathlib.AlgebraicGeometry.AffineScheme and its canonical stalk/localization map.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth;
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion and the
  affine quotient characterization.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback and projections;
  the product is dualized to the tensor algebra in the action-coordinate formulation.
- def-sfb-rational-point-local-jets owns the existing declarations in
  Sheaf.AlgebraicGeometry.TorusFixedLocalIdealJets: pointPrime, LocalRing, evaluate,
  Jet, jetMap, JetIdeal, quotientPoint. Their definitions are general in B, k and the
  coefficient algebra. The torus theorem itself is not used as the general theorem;
  differenceIdeal (which ranges over all points) is not misused for a subgroup.
- Sheaf.RingTheory.HopfActionModuleData: AlgebraCoaction, Counital, Coassociative.
- def-sfb-coordinate-hopf-algebra owns the existing declaration in
  Sheaf.AlgebraicGeometry.HopfCoactionLinearization: coordinateHopfAlgebra, exposing
  the canonical Mathlib.AlgebraicGeometry.Group.Affine instance with unbundled k.
- Mathlib.RingTheory.HopfAlgebra.Convolution: AlgHom.convGroup and convInv.
- Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary: dictionary,
  intertwines_iff and finite_dictionary, as proof imports for the last proof step.
- Remaining stated proof dependencies are imported from AffineFiniteTypeAlgebra,
  WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced, Properties,
  Spectrum.Prime.Topology, Pullbacks, TensorProduct.Maps, Localization.Ideal,
  Ideal.Quotient.Operations and AffineScheme. The finite-dimensional, tensor-product,
  and localization-at-prime definitions are publicly available through the reused
  local-jet module. No new helper is awaiting a downstream result.

Edge cases checked mathematically: n=1 gives N=2 and p=id; X=Spec k makes both
jet ideals zero; singular/nonreduced X (e.g. dual numbers) is included; arbitrary
positive characteristic is retained; disconnected smooth finite groups and trivial
G/H are included; H cannot be empty as it is a subgroup; empty X has no given x.
The density argument would fail for mu_p in characteristic p, which is correctly
excluded by Smooth G. It requires no smoothness of F or X. The c-family also has
N=0 and N=1 entries (zero algebra and residue k), which have canonical coactions;
these are harmless family-index completions of the stated N≥2 clauses.

Searches actually run via msearch.py NW lem-sfb-dense-fixed-local-ideal-jets:

- leanfinder: "An algebraic group action induces rational finite jets at a fixed point
  and the local fixed subscheme is the quotient by differences". Eight results about
  invariant quotient automorphisms, inertia and fixed subrings; no matching theorem.
- leansearch: "An affine algebraic group action gives rational representations on powers
  of the maximal ideal at a fixed point". Eight results about abstract representations,
  affine bases and invariants; no algebraic finite-jet statement.
- loogle: "HopfAlgebra, Algebra.Smooth, Ideal.Quotient". Zero results, with unknown
  identifier Ideal.Quotient (recorded as an unsuccessful query, not proof of absence).
- grep: "fixed.*[Ii]deal|[Jj]et.*[Rr]epresent|[Rr]ational.*[Cc]oaction", AlgebraicGeometry.
  Zero results in Mathlib's geometry directory.
- Direct rg on lean/WeilConjectures and lean/Sheaf, including differenceIdeal,
  localDifferenceIdeal, dense_fixed_local_ideal_jets and the node id. Found the torus
  specialization and shared Hopf/coaction/dictionary APIs, reused above; no general
  dense-subgroup statement. dag/lean_names_upstream.json has no match for the concept.

No STATEMENT-DISPUTED issue or statement correction. The expected sole sorry is the
named theorem. scompile.py passed sandbox and library compilation with no warnings.

## Second reading by NW

Performed a separate second pass through the node, source excerpts and completed Lean
file. This is a self-review because the dispatcher explicitly prohibited starting
other agents; independent delivery review remains with the maintainer.

I checked that density is density of the image of H in Spec k[G], rather than an
assumption that a chosen coordinate function test is injective. The subgroup law
comes from G's canonical Hopf structure. The inverse-action convention matches
Milne pp.86--87 and the node's gamma*. The fixed-functor hypothesis ranges over all
algebra maps q, rather than just rational points. The local automorphisms and quotient
isomorphism are pinned on B; J ranges only over H and maximal-ideal generators.
The induced coactions on both ideal quotients commute with their actual inclusions;
p is pinned on maximal-ideal representatives and is surjective and equivariant.
The residue field clause and the n=1 case were checked explicitly. No assumptions
on smoothness of X, linear reductivity, connectedness or characteristic slipped in.

During elaboration I made the existing coordinateHopfAlgebra interface a public
import, since its initial proof-only import hid the unbundled coordinate structure.
A missing parenthesis around the existential ideal was repaired. These are syntax
and import-visibility fixes, with no mathematical change. No new Lean definition or
repair of a dependency module is necessary; the ownership node below is added.


## Returned delivery repair

H2 of immutable head e96708733b53 is repaired exactly as requested. Removed
lem-sfb-torus-fixed-local-ideal-jets and lem-sfb-hopf-coaction-linearization from
stmt_deps: their theorem conclusions are not used in the statement. Replaced them
with def-sfb-rational-point-local-jets and the already landed
def-sfb-coordinate-hopf-algebra. Kept def-sfb-hopf-action-module-data, the actual
owner of AlgebraCoaction, Counital and Coassociative. The item differs from the
current base only in lean and stmt_deps. The delivery wrapper rebases the completed
sandbox onto its refreshed current branch.

The Lean file remains byte-identical to the returned delivery, SHA256
`d7312ef6536f9f05a20012f45d8b1e6516151f2c65c311362d4a63f03ba9b683`.
No mathematical signature, proof, import, or docstring was changed. The independent
return accepted the mathematics, normalization of all maps and edge cases; this
repair concerns definition ownership alone.

## New nodes

def-sfb-rational-point-local-jets records existing:true on
Sheaf.AlgebraicGeometry.TorusFixedLocalIdealJets, with the seven declarations
AlgebraicGeometry.TorusFixedJets.pointPrime, LocalRing, evaluate, Jet, jetMap,
JetIdeal and quotientPoint. These plain definitions at live lines 42--95 have no
choice and no postponed proof in their data. The source is Milne Lemma 13.4, p.255,
proof of Lemma 13.6, p.256, and affine action tensor evaluation in Section 4(d),
pp.86--87. It defines ker(x), B localized at ker(x), the quotients by maximal-ideal
powers, the quotient maps, image ideals as k-subspaces, composition with B→B/K,
and evaluation by the tensor product map. It assumes no action, finite type or
smoothness. For N=0, Jet is the zero algebra and JetIdeal is the image ideal zero;
for N≥1, the image is m/m^N. The statement makes this distinction explicitly.

Searches run again for this new ownership node, recorded verbatim in mathlib_searches:
LeanSearch query "local ring and finite jet algebra at a rational point of an affine
scheme" returned local-ring/stalk primitives, not the named seven-helper interface;
LeanFinder query "rational point kernel prime localization quotient maximal ideal
power jet algebra" returned smooth/etale loci and cotangent localization primitives;
Mathlib grep "pointPrime|quotientPoint|JetIdeal|def jetMap" returned zero hits.
Direct rg of WeilConjectures and Sheaf found the seven declarations in the existing
torus module, which are reused instead of duplicated. Exact helper-name and
rational-point-local-jets searches among DAG definition nodes found no existing
owner. tools/blueprint_refs.py search "local jets" returned zero blueprint matches;
the ancestor query reports null, matching the item's inherited ancestor. The new
node uses that same ancestor and prepends this item to its via chain.

Second reading of the repair: I reopened each of the seven declarations and matched
their literal bodies with the new definition-node clauses. In particular evaluate
is general in C/E/D, JetIdeal is an image ideal with restrictScalars k, and
quotientPoint is literal composition, with no dependence on the torus theorem.
The primary lean.statement matches pointPrime's signature verbatim. The seven
full names are listed in lean.declarations, and existing:true introduces no new
module. I reopened def-sfb-coordinate-hopf-algebra and confirmed that its
existing:true binding is precisely HopfAction.coordinateHopfAlgebra. Neither
removed theorem remains in stmt_deps. No other part of the accepted statement
needed a repair.
