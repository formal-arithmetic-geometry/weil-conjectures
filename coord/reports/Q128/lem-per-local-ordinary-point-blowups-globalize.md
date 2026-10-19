## Worker report

The module Sheaf.AlgebraicGeometry.LocalOrdinaryPointBlowupsGlobalize states
AlgebraicGeometry.local_ordinary_point_blowups_globalize, with its proof postponed by sorry.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.

Clause-by-clause correspondence:

- The scheme S has arbitrary universe u. IsIntegral S is the recorded integral-scheme
  definition; IsNoetherian S is Mathlib's locally Noetherian and compact scheme class.
  Its isNoetherian_iff_of_finite_iSup_eq_top identifies this with the finite affine cover
  by Noetherian rings specified in the node. hS is precisely the conjunction IsDomain
  and IsIntegrallyClosed on every stalk, without imposing global affine normality.
- r : Nat allows r=0. s : Fin r → S, hs : Function.Injective s and hclosed state
  distinct closed points. The open U is the complement of Set.range s, with its
  closedness supplied by the finite union of hclosed.
- S_i is Spec (S.presheaf.stalk (s i)), with its actual canonical S.fromSpecStalk map.
- n i is arbitrary, including zero. T i is the finite inverse chain indexed by
  the opposite ordered category Fin (n i + 1). t0 identifies its first scheme with S_i.
  The structural morphisms are the functor's maps to zero followed by (t0 i).hom.
  This uses isomorphisms for the displayed equalities T_i,0=S_i and Z_0=S;
  it neither changes the schemes up to isomorphism nor loses the base maps.
- hT asserts integral and stalkwise normal at EVERY local stage. It does not add
  Noetherianity or properness hypotheses for the local stages.
- c and hc are their closed-point centers. hover says they map to the closed point
  of the stalk spectrum. hbl identifies each actual adjacent arrow with the ordinary
  blowupMap of the vanishingIdeal of that closed singleton. This is the reduced
  center, not an arbitrary ideal with singleton support.
- The global chain Z has exactly sum_i n i arrows; z0 identifies its first stage with S.
  All structural morphisms are Z.map to zero followed by z0.hom.
- a gives monotone counts with a i 0=0 and final value n i. At each adjacent step
  exactly one count increases by one and every other count stays fixed. The active
  index exists at each step and is unique because its increase conflicts with the
  equality required of each other index. No extra order of scheduling is imposed.
- Each Z stage is integral, Noetherian and stalkwise normal. d and hd are reduced
  closed-point centers. Each arrow is the ordinary blowup at its displayed center,
  is proper, restricts to an isomorphism on the complement of that center, and its
  center maps to one of the original s i.
- For every i,j, IsPullback (q i j) (local structural morphism)
  (global structural morphism) (S.fromSpecStalk (s i)) says that the prescribed
  T_i,a_i(j) IS the base change of Z_j. IsPullback is the universal Cartesian-square
  predicate for the same chosen fibre-product notion as the recorded pullback.
  The following equality makes the adjacent squares commute. When the count stays
  fixed, the local map is an identity by functoriality, exactly the inserted arrows.
- For every global z over s i there exists t with q i j t=z, and the actual
  structural stalk map (q i j).stalkMap t is an isomorphism. This supplies the stated
  corresponding point and local-ring isomorphism, rather than an unrelated ring iso.
- The restriction of every global structural map to U is an isomorphism over U.
- Failure of IsRegularLocalRing at all prescribed centers implies its failure at
  every global center. This is the node's optional singularity clause, not a mandatory
  assumption. IsRegularScheme's recorded module supplies the same regular local ring
  predicate; the entire scheme need not be singular.
- If r=0 or all n i=0, sum_i n i=0. Fin (0+1) has one object and Fin 0 has no
  adjacent steps: z0 is precisely the identity tower up to its specified initial
  identification. There is no unnecessary nonemptiness assumption on the indices.

Dependency declarations read and used: Mathlib.AlgebraicGeometry.Properties,
AlgebraicGeometry.IsIntegral; Mathlib.RingTheory.IntegralClosure.IntegrallyClosed,
IsIntegrallyClosed (and IsDomain for normal domains); Mathlib.RingTheory.Noetherian.Defs,
IsNoetherianRing through Mathlib.AlgebraicGeometry.Noetherian, AlgebraicGeometry.IsNoetherian;
Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Spec;
WeilConjectures.Blowup.Gluing, Scheme.IdealSheafData.blowup and blowupMap;
Mathlib.AlgebraicGeometry.Morphisms.Proper, AlgebraicGeometry.IsProper;
Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, pullback (its universal-square
form CategoryTheory.IsPullback is used); Sheaf.AlgebraicGeometry.IsRegularScheme,
AlgebraicGeometry.IsRegularScheme and its imported IsRegularLocalRing. Reduced point ideals
use the existing Mathlib Scheme.IdealSheafData.vanishingIdeal. The stated proof dependencies
are imported, including the upstream audit-closed blowupFlatBaseChangeIso module.
No private copy of any notion is introduced.

Source read: literature/stacks-project/resolve.tex, section Modifying over local rings,
equation-equivalence, lemma-equivalence-fibre (0BFX), and the converse proof of
lemma-equivalence-sequence-blowups (0BFY). The node's ten proof steps are reproduced in
natural language in the theorem docstring, with each dependency named.

Edge cases: empty list of points; every length zero; mixed zero and positive lengths;
one point; arbitrary characteristic and arbitrary scheme universe; regular centers are
allowed; singular centers are required only conditionally; zero-dimensional integral base
admits the length-zero tower, while a positive-length reduced point blowup becoming empty
cannot meet hT. No dimension, excellence, or surface hypothesis was added.

Searches run using msearch.py Q128 for this item:

- leanfinder: "Finite towers of ordinary blowups at closed points globalize from the local
  schemes at finitely many closed points": 8 hits on finite-type morphisms, properness,
  normalization and affine transition limits, no matching tower theorem.
- leansearch: "A sequence of point blowups over a local scheme extends to point blowups
  on the original scheme": 8 hits on local-ring spectrum maps, stalks, residue fields,
  finite presentation and Scheme.mk; no tower globalization statement.
- loogle: the query consisting of quoted blowup and quoted localization: 0 hits.
- grep: blowup.*locali|locali.*blowup|point.*blowup.*sequence: 0 Mathlib hits.
- Direct rg in upstream WeilConjectures and lean/Sheaf for ordinary blowups, blowup towers
  and point blowups found the distinct normalized-resolution statements and the consumer
  RationalSurfacePointBlowupResolution.lean, not this globalization statement.
- Direct rg for the item id in WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  found only the consumer's proof-plan citation. Direct Mathlib rg found no declaration
  named local_ordinary_point_blowups_globalize.

No STATEMENT-DISPUTED flag or source correction is needed. The first compile caught only
finite-union/range syntactic conversion; the next compile caught a long line. Both were
fixed. All compilation uses the prescribed scompile.py wrapper.

## Second reading by Q128

The dispatched worker reread the node and full file after elaboration; no second agent was
started, as the dispatch explicitly forbids other agents. This is a separate rereading,
not a claim of independent-agent review. The maintainer's independent review remains required.

I checked the initial isomorphisms and actual structure maps, all hT quantifiers, the
reduced singleton ideal in hbl, the exact sum length, the count endpoints and single-index
increments, every global stage's three properties, all center support and properness clauses,
every Cartesian and arrow-compatibility square, the actual stalkMap isomorphisms and the U
restrictions, and the conditional singularity implication against the node. I specifically
checked that the local comparison arrows have direction T_i,a(j+1) → T_i,a(j) and that the
stalk map has direction O_Z,q(t) → O_T,t. The closure conversion was repaired by the existing
Set.range_eq_iUnion theorem; its inline proof constructs only a closed-set proof, not a
postponed theorem or data. No missing clause or added mathematical hypothesis was found.
