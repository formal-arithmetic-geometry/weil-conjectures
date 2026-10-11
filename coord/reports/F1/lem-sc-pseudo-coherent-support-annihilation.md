## Worker report

The module introduces `Scheme.IsSupportedOn` using vanishing after restriction to the quasi-compact open, and `Scheme.IsBoundedBelow` using vanishing of negative homology. It states `exists_perfect_annihilator` with the two perfect/pseudo-coherent cases and the perfect object, open restriction isomorphism, and zero tensor map conclusion. Dependencies used are `Sheaf.AlgebraicGeometry.PerfectComplex` (`Scheme.IsPerfect`), `Sheaf.AlgebraicGeometry.PseudoCoherentComplex` (`Scheme.IsPseudoCoherent`), and `Sheaf.AlgebraicGeometry.DerivedCategory` (`schemeDerivedCategory`).

Edge cases considered: empty open and zero complexes are covered by `IsZero`; the bounded-below bound permits every integer. Searches found no existing scheme-level support-annihilation or derived tensor declaration in Mathlib or the project. The file compiles with the expected `sorry` declaration warning suppressed by project options.

## Earlier second reading (a previous round; superseded)

The statement and definitions were reread against the source and dependency signatures; all binders are explicit and the module compiles remotely.

## Second reading by F1

I read the item JSON, its five proof steps, the delivered Lean, and all four statement
 dependency records and source signatures. I read Stacks perfect.tex at
`lemma-map-from-pseudo-coherent-to-complex-with-support` (0A9C), including the whole
statement and proof, in the local Stacks source `/home/ubuntu/c1-stacks-review/perfect.tex`.
The source assumes only a quasi-compact quasi-separated scheme and quasi-compact open
complement; it imposes no Noetherian, field, characteristic or boundedness assumption
in case (i). The node states exactly this source result and needs no correction.

Objects, hypotheses and conclusion, listed before comparison:

- A scheme Y: `(Y : Scheme.{u})`, the recorded Mathlib Scheme of def-pc-scheme.
  Verdict: same locally ringed-space notion, arbitrary universe u.
- Y quasi-compact and quasi-separated: `[CompactSpace Y] [QuasiSeparatedSpace Y]`.
  Verdict: exactly the two topological properties of the node; not separated or Noetherian.
- A quasi-compact open V and T = Y minus V: `(V : Y.Opens)` and
  `[CompactSpace (V : Set Y)]`. T need not be separately bundled: support is precisely
  vanishing after restriction to V. Verdict: same complement, including both extreme opens.
- P,Q in D_QCoh(Y) and alpha:P -> Q: `(P Q : schemeDerivedCategory Y) (α : P ⟶ Q)`
  with `hPqc : schemeDerivedQCohProperty Y P` and `hQqc` for Q. I opened
  DerivedCategory.lean: schemeDerivedCategory is D(O_Y), not D_QCoh(Y), and
  schemeDerivedQCohProperty requires every integer-degree homology sheaf to be
  Mathlib-quasi-coherent. The full subcategory is recorded alongside it; expressing
  its morphisms in the ambient category with these predicates is exactly equivalent
  because that subcategory is full. Verdict: repaired missing quasi-coherence.
- Case (i), P perfect: `Scheme.IsPerfect Y P` in the disjunction. I opened
  PerfectComplex.lean: every point has an open neighborhood with a derived restriction
  isomorphic to a bounded complex of direct summands of finite free modules.
  Verdict: the dependency's actual scheme-local perfectness, with no bounded-below
  condition on Q in this case.
- Case (ii), P pseudo-coherent and Q bounded below:
  `Scheme.IsPseudoCoherent Y P ∧ ∃ n : ℤ, ∀ k : ℤ, k < n → IsZero (... k ... Q)`.
  I opened PseudoCoherentComplex.lean: locally bounded-above finite free complexes,
  exactly the scheme characterization in dependency def-pur-pseudo-coherent-complex.
  Verdict: same disjunction and bound; no global finite ranks or fixed bound added.
- Q supported on T in either case: `hQ : IsZero (overFunctor ... V ... .obj Q)`.
  Exact restriction to an open vanishes precisely when all cohomology sheaves vanish
  there. Verdict: same support, factored outside the disjunction without altering it.
- There exists a perfect I: `∃ J : CochainComplex ..., Scheme.IsPerfect Y
  (DerivedCategory.Q.obj J)`. Here I is Q(J). Verdict: every derived object has a
  representative; no K-projectivity, strict perfectness or flatness imposed on J.
- There is a map I -> O_Y[0]: `∃ i : J ⟶ schemeUnitComplex Y`, giving Q(i).
  `schemeUnitComplex` is the actual sheaf tensor unit in degree zero. Any derived
  map to this object has a roof; taking the roof source as J realizes this choice
  without restricting the theorem. Perfectness is invariant under its quasi-isomorphism.
  Verdict: same existential map, not an arbitrary monoidal unit.
- That map is an isomorphism on V: `IsIso (overFunctor ... V ... .map
  (DerivedCategory.Q.map i))`. Verdict: isomorphism of this specific restricted map,
  not just an unrelated isomorphism of its source and target.
- The composite I tensor^L P -> P -> Q induced by i and alpha is zero:
  `Scheme.TensorAnnihilates Y J i P Q α`. Its definition resolves P by a K-flat N,
  identifies Q(N) with P by e, and composes Q(Tot(i tensor 1_N)), Q(t), e.hom and α.
  The degree-n unit summand condition fixes t to the canonical sheaf left unit action.
  All other summands have zero first factor, so the condition specifies t uniquely.
  Verdict: actual zero composite, explicitly dependent on i and alpha.
- Technical derived localization instances: one `[HasDerivedCategory.{w} ...]`
  and the same instance for every open, as required by the recorded perfect and
  pseudo-coherent dependencies. Verdict: shared D(O_Y) with its Mathlib Abelian
  instance, arbitrary morphism universe w; no chosen second Abelian structure.

Mismatches repaired:

1. The original last clause was `∃ β : I tensor P ⟶ Q, β = 0`. This is automatic
   and says nothing about alpha or the map to the unit. Replaced it by the actual
   tensor composite with the canonical unit action.
2. The original P and Q lived in D(O_Y) with no quasi-coherence assumptions.
   Added the two recorded predicates; this restores the node's D_QCoh(Y).
3. The arbitrary `[MonoidalCategory (schemeDerivedCategory Y)]` did not identify
   its tensor with derived tensor or its unit with O_Y[0]. Removed it, using the
   fixed `SheafOfModules.monoidalCategory Y.sheaf` and K-flat total tensors instead.
   No monoidal structure on D(O_Y) is assumed.
4. Removed the untracked local `Scheme.IsSupportedOn` and `Scheme.IsBoundedBelow`
   definitions; the theorem now uses the explicit restriction/homology conditions.
5. Expanded the abbreviated proof docstring into all five DAG steps, naming the
   nodes used, the n=0 case, and the roof/K-flat representation of the last step.
   Added the standard copyright/license header. The new predicate has its own node.
6. Combined compilation initially reported a duplicate universe name u between
   the two modules; renamed the new module's universes uT,wT. No mathematical
   change was needed. The combined compile then finished cleanly in 4.5 seconds.

Edge cases: V empty imposes no restriction on support; V = Y forces Q = 0 and
permits the identity unit annihilator. The empty scheme and zero P or Q are allowed;
no nonempty-point or nonzero-object instance occurs. Bounds are arbitrary integers,
including zero and negative bounds. The theorem does not quantify over a generator
index set; the proof's n=0 case is documented. Structure sheaves can have arbitrary
characteristic. Universes u,w (and uT,wT in the predicate) are explicitly bound, with
no independent test-object universe causing a vacuous condition. All existential
representatives are required to exist rather than supplied by an unconstrained
hypothesis. No data uses sorry, and the sole theorem remains `by sorry`.

Independent searches (actual msearch.py records in searches.jsonl):

- LeanSearch: "morphism from perfect complex annihilates morphism supported on
  closed complement" and "zero composite induced by tensoring morphism to unit
  using K flat complex": service returned Internal Server Error, recorded unavailable.
- Loogle: `"annihilator"`: compiler constant folders and linear algebra dual
  annihilators, no derived support-annihilation statement.
- LeanFinder: "derived tensor action of a map from a complex to the structure
  sheaf kills a derived morphism using K flat resolution": Tor and module-flat
  exactness results only, not sheaf complexes or their derived tensor action.
- Mathlib grep: `perfect_annihilator|IsSupportedOn|IsBoundedBelow` and
  `TensorAnnihilates|tensorAnnihil|derivedTensor.*[Mm]ap`: zero hits.
  `tensorAnnihilates|TensorAnnihilates|mapBifunctorMap` in Algebra/Homology finds
  mapBifunctorMap and its naturality facts, which the new predicate uses directly.
- Project/source rg for TensorAnnihilates, tensorAnnihil, schemeUnitComplex and
  exists_perfect_annihilator finds no prior notion/declaration. Broader derivedTensor
  searches find source Etale/Derived/Tensor.lean:92 and ProEtale/Derived/Tensor.lean:84;
  I opened both signatures. They concern A-valued small-etale/proetale sheaves,
  not structure-sheaf modules on the Zariski site. The project's derivedTensor is
  likewise the proetale coefficient-ring version. They cannot serve this node.
- DAG search for support, tensor action, tensor vanishing and annihilation: existing
  def-pc-derived-tensor-cohomology-vanishes is vanishing of a homology object after
  tensor with a degree-zero sheaf, not a zero morphism. Existing
  lem-pc-derived-tensor-action-naturality is a ring base-change scalar-action theorem,
  not this scheme-level predicate. Neither is duplicated.

The main theorem's `lean.statement` and the new node's `lean.statement` were extracted
with tools/stage2_delivery.py and kept verbatim equal to their source signatures.
The unit statement, node statement, proof and all old dependency fields are unchanged.

## New nodes

`def-sc-derived-tensor-annihilates` supplies the missing scheme-level zero derived
 tensor-action predicate and the structure-sheaf complex used in its type. Its source
is the tensor composite in Stacks 0A9C and the K-flat computation in sites-cohomology.tex
Section 06YL (06YS, 06YU). I read that section's K-flat definition, resolution theorem,
quasi-isomorphism preservation and the independence-of-resolution construction.
The definition matches those sources: tensoring with K-flat N computes the derived
map in the first variable for any J; the unit action is fixed summand by summand.
The predicate's source and target objects, the map i, alpha, representative N,
identification e, canonical t and zero composite are all introduced explicitly.
The node cites the existing scheme, derived category, cochain complex, K-flat and
complex-tensor nodes; it copies no definition of those notions. Its Mathlib/source/
project/DAG searches are listed above and recorded on the node. The generic KFlat.lean
signature was read: CochainComplex.IsKFlat tensors an arbitrary acyclic complex on
its left, exactly the orientation used here. The tensor dependency is the recorded
mapBifunctor with the sheaf monoidal structure; mapBifunctorMap gives its map on i.
The new node has definition/split status, empty proof fields, null mathlib_match,
none audits, the item's chapter/unit, worker/group/item creation record, and ancestor
lem-sc-finite-duality with this item prepended to the full computed ancestor via path.
No dependency module is necessary: all five notions used by this predicate already
have usable declarations. Neither of its definitions contains sorry or an internal
postponed proof.

Dry-run metadata repair: preflight computes the full blueprint ancestor path recursively;
the sandbox item stores only its immediate via. Updated the new node to the full nine-entry
path printed by preflight. No existing blueprint field was changed.
