## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusSimpleRootIsomorphismCriterion`
states `AlgebraicGeometry.torus_simpleRoot_isomorphism_criterion`. Its sole theorem
has proof `sorry`; it introduces no definition. The item node changes only in `lean`.
No new nodes, dependency repairs, or statement correction are needed.

Source read: Milne, Algebraic Groups (2017), printed p.492, 23.24 and the paragraph
completing 23.18. The latter explains why torus and geometric-point bijectivity alone
are insufficient and uses root-group isomorphisms to exclude infinitesimal kernels.
The source's projection is generalized exactly as the already-reviewed node says.
The latest blueprint proof `sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), was also read;
the node's blueprint ancestry records the compatible-rank-one-graph support route.

Hypothesis and clause correspondence:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Group schemes and homomorphisms: `H G S T : Grp (Over (Spec (.of F)))`,
  `iS`, `iT`, and `f` are morphisms in that category, hence group homomorphisms.
- Affine finite-type, smooth connected reductive H and G: `hH`, `hG` use the
  dependency's `ReductiveTorusCentralizer.IsReductive`. Its `IsAlgebraic` component
  is `IsAffine` plus `LocallyOfFiniteType` and `QuasiCompact`; it includes smoothness
  and geometric connectedness, and excludes nontrivial smooth connected normal
  unipotent subgroups. Over the given algebraically closed F the base extension
  to its algebraic closure is an equivalence, so this is the stated reductivity.
  The inherited unipotence predicate uses a faithful matrix representation, not
  an abstract group-theoretic notion of unipotence.
- Closed maximal tori: `hS`, `hT : IsMaximalTorus ...` include closed subgroup
  inclusions, torus structure and maximality among torus inclusions. `hsplitS` and
  `hsplitT` give actual isomorphisms with the dependency's `splitTorus F r`.
- Surjectivity on underlying spaces: `hf : Surjective f.hom.hom.left`. This is
  scheme-topological surjectivity, not surjectivity of rational points.
- Torus restriction: `a : S ≅ T` and `ha : iS ≫ f = a.hom ≫ iT`.
- The target's actual character and cocharacter groups are the two displayed
  `Additive` group-scheme Hom types. The two `IsCommMonObj` witnesses expose their
  canonical abelian group structures, as in `reductive_borel_pair_structure`.
- Root datum and simple base: `Φ`, `P : RootDatum Φ ...`, `base : P.Base`, `hred`.
  `hroot` identifies each abstract root with its character. `hpair` pins the integer
  pairing to composition with the integer power morphism of Gm. `aG` and `hconj`
  identify the action with conjugation by `iT`; `hweights` identifies Φ with exactly
  the nonzero character weights on the tangent space. These specify the datum
  referred to by the node, rather than assuming an unrelated root system or
  imposing that roots span the full character lattice. The `Base` coroot clauses
  agree with the dependency's own representation of a simple-root base.
- Fixed target root subgroups: `U : Φ → Grp ...`, `iU`, and `hU`. Each is closed,
  smooth, connected, stable under T, and its tangent image is exactly its root
  character weight space. `Nonempty (Ga ≅ U β)` is its additive-group isomorphism.
  These are precisely the root subgroups specified by the recorded parametrization
  theorem; its uniqueness identifies any such choices with those of the node.
- Both signs of every simple root: `∀ (α : base.support) (ε : Bool)` in `hlift`.
  The witness `β : Φ` satisfies `β.val = if ε then α.val.val else -α.val.val`;
  true is +1 and false is -1. The existential witness ensures this condition is
  not an implication with an accidentally missing negative-root index.
- Lifted subgroup: existential `V`, `iV : V ⟶ H`, with
  `IsClosedSubgroupScheme iV.hom.hom`, `Smooth V.X.hom`, `ConnectedSpace V.X.left`,
  and `v : Ga ≅ V`. It is the given smooth connected closed additive subgroup.
- Restriction isomorphism: `e : V ≅ U β` and `iV ≫ f = e.hom ≫ iU β` ensure that
  e is exactly f restricted to this subgroup, not an unrelated isomorphism.
- Normalization and pulled-back root action: the final universal equation in
  `hlift` says conjugation by `s ≫ iS` sends `v(x)` to
  `v(multiplicativePointCoordinate (s ≫ a ≫ β) * x)`. Its coefficient is the
  character β evaluated at a(s), hence a*(εα). This explicit formula also gives
  normalization: every V(A)-point has the unique coordinate x through v, and its
  conjugate has the displayed coordinate. No extra action or stability predicate
  needs to be invented. The condition is imposed for the chosen parametrization,
  exactly as the node's 'for an isomorphism v'; it is invariant under replacing
  v by another group-scheme parametrization.
- Every commutative F-algebra extension: `∀ (A : Type u) [CommRing A] [Algebra F A]`
  and all S(A)-points and x : A. The test-algebra universe is the field/scheme
  coordinate universe, as in the recorded dependencies. It includes the coordinate
  algebras and universal points, so these equations are morphism identities and
  retain their meaning for arbitrary further scalar extension. In particular it
  does not restrict to fields, reduced rings, or rational points.
- Conclusion: `IsIso f` in the category of group schemes, so the inverse is a
  group-scheme homomorphism. There is no separability or reduced-kernel hypothesis.

Dependency declarations actually read and used (module — names):

- `Mathlib.Algebra.Field.Defs` — `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` — `IsAlgClosed`, the algebraically-closed
  clause of the algebraic-closure dependency's Mathlib match.
- `Mathlib.CategoryTheory.Monoidal.Grp` — `GrpObj`, `Grp`, its homomorphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` — `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` (via the recorded interfaces).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth` — `Smooth`.
- `Mathlib.Topology.Connected.Basic` — `ConnectedSpace` (includes nonemptiness).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact` —
  `LocallyOfFiniteType`, `QuasiCompact` inside `IsAlgebraic`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure` —
  `reductive_borel_pair_structure`, especially its exact Hom lattices, `RootDatum`,
  `Base`, composition pairing and character-weight identification.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations` —
  `TorusCharacterTangent.reductive_root_subgroup_parametrizations`,
  `additiveParameterPoint`, `multiplicativePointCoordinate`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes` — `affine`, `additive`,
  `multiplicative`, with their existing group structures.
- The reductivity/maximal-torus terminology and `TorusCharacterTangent.weightSpace`
  and `.IsStable` are the exact definitions exposed by these dependency modules;
  no copies or new predicates are introduced.

The recorded, stated proof dependencies are imported without `public`: affine
flat-image factorization, smooth geometric reducedness, closed immersions, reduced
schemes, rank-one reflections, root-datum lattice embedding, rational/integral base
spans (`Base` and `BaseExists`), reflection induction (`Base`), and the torus
self-centralizer. The current records of normal-subgroup torus finiteness,
isogeny root-power laws, and faithfully-flat quotient universal property have no
Lean module yet, so those three cannot be imported at this stage. Their mathematical
uses are retained in the complete eight-step theorem docstring. Missing proof
statements do not obstruct stating this item, and are not statement prerequisites.

Edge cases checked before writing:

1. Empty Φ and empty base (torus-only and trivial-group cases): no `Nonempty`,
   positive rank, or inhabited index assumption occurs. `hlift` is vacuous for
   the empty base. The conclusion is still the global isomorphism assertion.
2. Positive characteristic, especially characteristic two: negative roots mean
   inverse characters, not negative differentials or field scalars. Characters
   remain distinct even when their differentials coincide.
3. Infinitesimal kernels and test algebras such as dual numbers are retained.
   Surjectivity and torus isomorphism alone are not substituted for the lifted
   root-group hypotheses, which rule out inseparable root-power kernels.
4. Torus ranks zero and central torus factors: roots are not required to span
   the character lattice, and the two split ranks are existential natural numbers.
5. The zero test algebra is allowed by `[CommRing A] [Algebra F A]`; the universal
   point formulas remain valid. ConnectedSpace excludes the empty group scheme.
6. The torus square and root-group square are required, so arbitrary isomorphisms
   of tori or additive groups cannot be passed as though they were restrictions.

Searches actually run with msearch.py (results recorded by the tool in searches.jsonl):

- LeanFinder: 'A surjective homomorphism of reductive group schemes is an isomorphism
  if it is an isomorphism on maximal tori and lifts simple root subgroups
  isomorphically'. Eight hits; only generic scheme surjectivity/closed-immersion
  facts and Galois-category automorphism surjectivity, no matching criterion.
- Loogle: 'RootPairing.Base, IsIso'. Zero hits; diagnostic 'unknown identifier
  IsIso', so this query is inconclusive rather than evidence of absence.
- Mathlib grep: 'isogeny|simple.*root.*isomorph' in AlgebraicGeometry. Zero hits.
- LeanSearch: 'A surjective homomorphism of reductive group schemes that is an
  isomorphism on maximal tori and simple root subgroups is an isomorphism'. Eight
  hits including `Flat.isIso_of_surjective_of_mono` and the surjective closed
  immersion criterion, neither supplies the stated group-scheme criterion.
- Further Loogle query: 'CategoryTheory.IsIso' (generic isomorphism interface).
- Direct rg of the exact item id and `torus_simple|simple_root.*iso|`
  `torus.*isomorphism.*criterion` in both `lean/WeilConjectures` and `lean/Sheaf`:
  only the compatible-rank-one-graph proof plan mentioned this criterion, with no
  declaration stating it. A wider isogeny/simple-root scan confirmed no duplicate.

Validation: scompile.py compiled the sandbox module and its intended library
module cleanly (9.4 s and 2.8 s in the successful run). The initial syntax typo in
one binder was corrected before this success. No non-sorry warnings remain.
No STATEMENT-DISPUTED issue or source correction was found.

## Second reading by Q22

This is a separate rereading by the same dispatcher-started worker; no independent
worker was started, as the task explicitly prohibits starting agents. The independent
maintainer review remains the review of this delivery.

I reread the entire node and the complete final signature against the p.492 source
passage. I checked that the torus square uses iS followed by f, the lift square uses
V followed by f, and the character coefficient uses S followed by a followed by the
signed target character. The iso e is tied to the restricted homomorphism, while v
is the separate Ga parametrization. The target roots and their pairing are pinned
to actual scheme characters and conjugation weights. Smoothness, connectedness,
closedness, both signs and every test algebra are present. An explicit normalized
subgroup predicate on V would duplicate the already stronger displayed action
formula, so none was added. No nonempty-base condition, root-span assumption,
reducedness or separability condition slipped into the signature. The only drafting
mismatch found was a surplus parenthesis in hpair; it was fixed and the resulting
module compiled. No mathematical change to the node was necessary.
