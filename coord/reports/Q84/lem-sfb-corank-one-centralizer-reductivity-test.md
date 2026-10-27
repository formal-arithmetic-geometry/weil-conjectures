## Worker report

This delivery states `AlgebraicGeometry.ReductiveTorusCentralizer.corankOneCentralizer_reductive_iff`
in `Sheaf.AlgebraicGeometry.GroupScheme.CorankOneCentralizerReductivity`. Its only proof is
`sorry`; it introduces no definitions. I read the complete item, all eight original statement
dependencies and their recorded definitions, the newly cited already-landed definition nodes,
and the full source signatures/docstrings. There is no released repair note for this item.

Source checked: Brian Conrad, Reductive Group Schemes, Lemma 3.1.10, printed p.87,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, PDF page 87 (zero-based 86).
The preceding paragraph explicitly specifies the quotient by the saturation of Z alpha;
the lemma specifies the reduced identity component of the kernel and the centralizer criterion.
The given node and its seven-step proof agree with this source. No statement correction.

Clause-by-clause translation:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The group schemes are `H T : Grp (Over (Spec (.of k)))`. Morphisms in `Grp` are
  scheme morphisms respecting the multiplication. Affineness is `[IsAffine H.X.left]`;
  finite type is `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`;
  smoothness is `[Smooth H.X.hom]`; connectedness is `[ConnectedSpace H.X.left]`.
- The closed maximal torus inclusion is `i : T ⟶ H`, `hT : IsMaximalTorus i`.
  This predicate includes closedness, the existing torus predicate (split after algebraic
  closure), and maximality among all closed torus inclusions. Since k is algebraically
  closed, this is precisely isomorphism with G_m^r over k, with r = 0 allowed.
- `hself` is equality of `centralizerPoints i A` and the image of T(A) for every
  commutative k-algebra A. Its existing definition quantifies over all A-algebra
  extensions B and T(B), so it says the scheme-theoretic C_H(T) = T.
- `a : ModObj T.X H.X` and `ha` specify the conjugation action, as the composite
  of i times the identity with `CategoryTheory.GrpObj.conj H.X`. This is the
  actual canonical action, not an arbitrary representation.
- The characters X are the actual group-scheme homomorphisms
  `T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)`. No differentiated characters
  are used. `Ψ` is a Set of exactly these characters, with `hΨ` saying membership
  is equivalent to a nontrivial character and nonzero `TorusCharacterTangent.weightSpace`.
  Multiplicative character notation renders additive alpha != 0 as `χ.hom.hom ≠ 1`.
- `GrpObj.Lie H.X` underlying the existing weight space is the canonical relative
  tangent space at the identity (dual of e^* Omega). `tangentPoint` identifies its
  vectors with dual-number points. Over algebraically closed k, testing characters
  on T(k) is equivalent to their scheme action, since split-torus points are dense.
  In particular, these weights retain characters divisible by the characteristic.
- `S α` and `j α` specify T_alpha inside the actual `GrpObj.ker α.val.hom.hom`.
  `hS : IsLargestSubtorus (j α)` says it is a closed torus in that kernel through
  which every torus subgroup of the kernel factors. This is the very same subgroup
  as Spec k[X/L_alpha], not an arbitrary torus or a replacement assumption. To see
  the equivalence, X is free of finite rank, L_alpha = X intersect Q alpha is
  saturated of rank one, and its quotient is free of rank rank(X)-1. The induced
  group-algebra quotient kills alpha. Any torus in ker alpha kills L_alpha:
  n*x = m*alpha implies n times its restricted character is zero, and a torus's
  character lattice is torsion-free. Thus it factors uniquely through that quotient.
  This proves the largest-torus and codimension-one descriptions agree, including
  nonprimitive alpha. The group algebra itself is not redefined.
- The composite subgroup inclusion into H is
  `j α ≫ Grp.ofHom (GrpObj.kerι α.val.hom.hom) ≫ i`.
  `C α`, `c α`, and `hc` specify a closed subgroup of H. `hC` identifies its points
  with `centralizerPoints` of this composite, on every commutative k-algebra A.
  This retains all further algebra extensions B and nonreduced test algebras.
  Specifying a representative by its complete universal property is independent
  of its choice and supplies precisely the centralizer C_H(T_alpha) in the node.
- `IsReductive H ↔ ∀ α : Ψ, IsReductive (C α)` is the claimed equivalence.
  The existing reductivity predicate uses affine finite type, smoothness, geometric
  connectedness, and absence of nontrivial smooth connected normal unipotent closed
  subgroups after algebraic closure. Over the already algebraically closed k, these
  are exactly the node's reductivity conditions. The existing unipotence predicate
  is a faithful closed matrix representation with (r(x)-I)^N=0, N>0, on geometric
  points. No characteristic restriction or nonemptiness condition on Ψ is imposed.

Dependency declarations reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (from the algebraic-closure node).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, `Grp.ofHom`;
  the project's group-scheme Defs supplies kernel, kernel inclusion, and subgroup predicates.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its public quasi-compact dependency:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace` and
  its canonical group/module structures. Imported as the original tangent-space dependency;
  the character-weight interface uses the equivalent upstream `GrpObj.Lie` implementation,
  defined in `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`: `IsMaximalTorus`,
  `IsReductive`, `centralizerPoints` in namespace `AlgebraicGeometry.ReductiveTorusCentralizer`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `MultiplicativeType.IsLargestSubtorus`,
  `IsTorus`, `splitTorus`.
- `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`: `TorusCharacterTangent.weightSpace`.

The last three corresponding definition-node ids are added to stmt_deps because they
are already landed and are used by the signature. No new nodes or dependency repairs.
Available proof dependencies are plain imports: torus-fixed-scheme smoothness, smooth
ambient normality, rational tangent-cotangent duality, group-like group-algebra basis,
and finite torsion-free module bases. The remaining proof nodes have no Lean record
or Mathlib match yet. The docstring records all seven proof steps for stage 3.

Edge cases checked before drafting and again against the signature:

- H=T (including H=T=1): there are no nonzero adjoint weights, so the right side
  is a universal quantifier over the empty subtype. There is no omitted existential
  choice of a weight or nonempty-family hypothesis.
- T=1 with C_H(T)=T forces H=1 as a represented functor; allowed.
- Rank-one T: T_alpha is the trivial torus and its centralizer is H itself.
- Character p times a primitive character in characteristic p: the kernel may have
  a nonreduced mu_p factor; its largest torus is still the saturated-quotient torus.
  Neither a zero differential nor a nonreduced identity component is substituted.
- G_m acting nontrivially on G_a: the relevant corank-one centralizer detects the
  nontrivial unipotent radical. The statement has no reductivity premise.
- Test algebras share the field/scheme universe u; they include coordinate rings
  and dual numbers, with no smaller independent universe making a condition vacuous.

Searches actually run (msearch.py Q84 and this item):

- LeanFinder: “A smooth connected affine algebraic group with self centralizing maximal
  torus is reductive if and only if all centralizers of corank one subtori defined by
  nonzero adjoint character weights are reductive”. Eight abstract Lie-algebra/Cartan
  hits; no algebraic-group scheme criterion.
- Loogle: `AlgebraicGeometry.IsReductive, AlgebraicGeometry.IsTorus, AlgebraicGeometry.GroupScheme`.
  Zero hits, unknown identifier AlgebraicGeometry.IsReductive.
- grep: `reductive|[Cc]orank|[Ss]ubtorus` in Mathlib AlgebraicGeometry. Zero hits.
- LeanSearch: “saturated subgroup generated by one character of a torus and its kernel
  subtorus”. Eight results about saturated abstract subgroups and unrelated character
  modules; no scheme-theoretic torus construction. The general subgroup results do
  not replace the already existing largest-subtorus predicate.
- rg in lean/WeilConjectures and lean/Sheaf for corank, IsReductive, IsUnipotent,
  IsMaximalTorus, centralizer/torus, weight-space definitions and character saturation.
  Found the reused interfaces above; no copy of this theorem. Node-id search in
  lean/WeilConjectures also returned no match.
- rg for `corankOneCentralizer_reductive_iff` in dag/lean_names_upstream.json,
  lean/WeilConjectures, and lean/Sheaf returned no existing declaration.

Validation: scompile.py compiled the module in sandbox and actual library module modes,
clean, within the default 60-second limit. Explicit `autoImplicit false`, universe u,
module mode and public statement imports; no auxiliary theorem, private definition,
file-local notation, or diagnostic command remains. No STATEMENT-DISPUTED or node fault.

## Second reading by Q84

Author's second pass, not an independent review: I reopened the node and final module
and checked each binder and conclusion. The finite-type pair and smooth/connected/affine
instances match H. hT includes exactly the closed maximal-torus condition. hself uses
full centralizerPoints rather than rational-point commutation. ha fixes conjugation;
hPsi (spelled hΨ in Lean) tests actual torus characters, so characteristic-p weights
are retained. hS specifies the largest torus in the genuine kernel, which agrees with
the saturated lattice formula by the torsion-free argument above. hc and hC fix full
scheme-theoretic centralizer representatives. The conclusion is a biconditional over
all weights and includes the empty set. No new definitions, extra characteristic
hypotheses, omitted cases, hollow maps, or arbitrary representations were found.
The first draft expanded the centralizer condition inline; I replaced that expansion
by the existing centralizerPoints declaration composed with Grp.ofHom of the kernel
inclusion. This removes duplicate terminology without changing any condition. Added
the already-landed definition-node citations for the three reused interfaces and the
newly available torus-fixed-scheme proof import. Maintainer independent review follows delivery.
