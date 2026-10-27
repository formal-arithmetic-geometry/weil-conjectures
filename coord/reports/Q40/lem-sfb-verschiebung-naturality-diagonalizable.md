## Worker report

Item: lem-sfb-verschiebung-naturality-diagonalizable, Q40 stage 2.
Module: Sheaf.AlgebraicGeometry.VerschiebungNaturalityDiagonalizable.
The statement and all original dependency lists are unchanged. No new node or dependency
repair is needed. Seven theorem statements, all with whole-proof `sorry`, state the seven
clauses of the item. One real-data helper `verschiebungCoordinate` is the composition of the
recorded `projection` with the recorded `iteratedComul`. It introduces no alternative
Verschiebung: dependency `Maps` specifies its coordinate map by exactly this formula.

Source read directly: literature/milne-algebraic-groups_iAG2017.pdf, printed pp.224–225
(Definition 11.39(a)–(c), and Proposition 11.40) and pp.231–232 (Chapter 12(b), group-algebra
Hopf formulas and Remark 12.6). The prose in Definition 11.39 reverses the coordinate arrow
in one sentence, but its diagram and functoriality equation give precisely the direction
used by the existing dependency and this delivery. No correction to the DAG is required.

Hypothesis and clause correspondence:

- Field and positive characteristic: `(k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p]`. Positive characteristic of a field is prime; these binders are the standard
  equivalent encoding of the source's characteristic p>0, including p=2.
- Affine commutative finite-type k-group schemes: `G H : Scheme.{u}`, their `Over (Spec
  (.of k))`, `IsAffine`, `GrpObj`, and `IsCommMonObj` instances. Finite type is exactly
  `LocallyOfFiniteType` and `QuasiCompact` of each structure morphism, as the recorded
  definition node specifies. Explicit `include` commands keep these hypotheses in the
  signatures even when they occur only in the intended meaning of the coordinate operations.
- The twist is the dependency's `twist k p C`. Its second-factor scalar structure is the
  dependency's `twistAlgebra`; `pure k p C a c` is a tensor a tensor c; `first` is a tensor 1.
  `verschiebungCoordinate` is `projection.comp (iteratedComul ... p)`; dependency `Maps`
  identifies its spectrum with the canonical V. Thus coordinate equalities here are exactly
  scheme-morphism equalities by fully faithful affine Spec, rather than assertions on just
  field-valued points. All universes and variables are explicitly declared; autoImplicit=false.
- Naturality: `verschiebung_naturality` quantifies over `f` in the Over category and
  `[IsMonHom f]`. `ft` is specified on every `pure a b` by `pure (f.left.appTop a) b`, which
  uniquely specifies f^(p) on coordinates. Its final equation is
  ft(v_H(a)) = v_G(f*(a)), the contravariant form of f V_G = V_H f^(p).
- Arbitrary field extensions: `verschiebung_baseChange` quantifies over any field K with
  an algebra structure over k. `CharP K p` records the inherited characteristic, not a
  separability or perfection condition. The coordinate algebra is K tensor_k Γ(G,top),
  using the ordinary left K Hopf structure from Mathlib. The comparison θ is an actual
  K-algebra equivalence and its pure-tensor formula specifies it uniquely. The final formula
  sends v_(G_K)(a tensor c) to a tensor v_G(c). The factor a^p appears in θ on a twisted
  tensor, while scalar a is unchanged in the compatibility formula. No Frobenius inverse
  is assumed or used, including when k or K is imperfect.
- Finite products: `verschiebung_product` gives the canonical twist comparison for the
  coordinate ring Γ(G,top) tensor Γ(H,top), specified on `(a tensor b) tensor c`, and sends
  its V coordinate map to v_G(a) tensor v_H(b). Products of affine schemes have exactly
  these coordinate Hopf algebras. `verschiebung_emptyProduct` gives the terminal group
  separately: on k, v(a)=1 tensor a. Binary and nullary compatibility are the usual
  equivalent specification of compatibility with every finite product, by iterating
  binary products and reindexing a finite index set. In particular the empty product is
  explicitly included, not excluded by a nonempty hypothesis.
- Closed subgroups: `verschiebung_closedSubgroup` uses `i : H.asOver ... ⟶ G.asOver ...`
  with `[IsClosedSubgroupScheme i]`. It assumes the coordinate formula v_G(a)=η ε(a) and
  concludes the same formula for H=N. The coordinate of the zero group homomorphism is
  η composed with the counit. It is not the zero linear map (which sends 1 to 0).
- Quotients: `verschiebung_quotient` quantifies over a homomorphism q:G→H=Q with
  `q.left.appTop.hom.FaithfullyFlat` and `.FinitePresentation`. For affine morphisms these
  are exactly faithful flatness and finite presentation. The conclusion is v_Q(a)=η ε(a)
  under the same vanishing assumption on G. Finite presentation is retained even though
  the cancellation proof only uses faithful flatness. These are the represented fppf
  quotients specified by the item, without adding a section or a point-surjectivity premise.
- Diagonalizable groups: `verschiebung_diagonalizable` binds M with `AddCommGroup` and
  `AddGroup.FG`. The ring is Mathlib's existing `AddMonoidAlgebra k M` with its standard
  Hopf structure, whose basis coproduct is e_m tensor e_m and counit is 1. The conclusion
  is a k-algebra equivalence v to its Frobenius twist, equal on every element to the
  canonical `verschiebungCoordinate`, together with v(e_m)=`first ... e_m`. Spec reverses
  this to the asserted isomorphism V of D_k(M), with exactly the requested coordinate map.
- No smoothness, connectedness, reducedness, algebraic closure, perfection, finite group
  order or torsion-freeness assumption appears.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180), through def-weil-field.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` (line 43), and
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsMonHom` (213), `IsCommMonObj` (1222), as the
  def-sc-group-scheme record specializes them to schemes over Spec k.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` (43) and
  `...QuasiCompact`: `QuasiCompact` (43), through def-weil-finite-type-morphism.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme` (76–82) and
  `IsClosedSubgroupScheme` (94–101); both full signatures and docstrings read. The latter
  includes the former and the closed immersion. No private subgroup predicate is introduced.
- `Sheaf.AlgebraicGeometry.AffineGroupFrobeniusVerschiebung`: full module read, in particular
  `twist`, `twistAlgebra`, `first`, `pure`, `projection`, `iteratedComul`, `Maps`, `GroupMaps`
  and `frobenius_verschiebung`. The latter gives the group homomorphism and identifies the
  coordinate map with the helper used here. All statement dependencies are already usable.
- `Mathlib.RingTheory.TensorProduct.Basic`: `instCommRing` (478), `includeLeft` (311),
  `includeRight` (323), `ext` (353); `...Maps`: `productMap` (810) and
  `productMap_apply_tmul` (816). These are the recorded mathlib_match of
  lem-weil-pbc-algebra-tensor-pushout-universal-property; signatures and docstrings read.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` (470), `Spec.map` (479), and
  `...GammaSpecAdjunction`: `Spec.homEquiv` (579), through def-weil-affine-spectrum.
- Proof imports: `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` exposes the recorded
  base-change and injectivity results. Read `Module.FaithfullyFlat.instTensorProduct`,
  Basic.lean 558–566, and `Module.FaithfullyFlat.tensorProduct_mk_injective`, Algebra.lean
  85ff. `RingHom.FaithfullyFlat` is the ring-map version of the recorded faithfully-flat
  definition. `LinearMap.baseChange` in TensorProduct/Tower.lean 661 is the recorded scalar
  extension notion; its signatures and pure-tensor formula were read.
- The proof-only lem-sfb-symmetric-invariant-frobenius-projection has no Lean declaration
  on the read base, so there is no module to import for it. Its naturality and orbit formulas
  are named in the docstrings as the proof plan, without creating a duplicate statement.

Searches actually run:

1. msearch.py leanfinder: `Verschiebung naturality affine commutative group schemes
   diagonalizable group algebra Frobenius twist`. Eight hits included
   WittVector.map_verschiebung and WittVector.verschiebung_frobenius_comm, and affine-space
   functoriality. They are not this group-scheme statement or this canonical construction.
2. msearch.py loogle: `"verschiebung"`. Twelve hits, all WittVector declarations; no match.
3. msearch.py grep: `Verschiebung|verschiebung|baseChange`, subdirectory
   `RingTheory/HopfAlgebra`. Zero hits. Read TensorProduct.lean and MonoidAlgebra.lean
   separately to use their existing Hopf instances.
4. msearch.py leansearch: `Verschiebung of affine group schemes naturality field extension
   products diagonalizable groups`. Eight hits on affine spaces, AffineScheme.ofHom and
   isAffineHom_isStableUnderBaseChange. None states any missing clause.
5. rg of `Verschiebung|verschiebung` in lean/WeilConjectures, and the required node-id grep:
   no hits. rg in lean/Sheaf found the recorded AffineGroupFrobeniusVerschiebung and the
   specialized LengthTwoWittExtensionVerschiebung. The latter computes V only for W₂ and
   G_a, so is not an existing match for this general theorem.
6. rg of diagonalizable/group-algebra terms in lean/Sheaf found DiagonalizableGroup.lean:
   `AlgebraicGeometry.diagonalizableGroup` already defines Spec of this standard group algebra.
   Its full module was read. This delivery uses Mathlib's same group algebra and Hopf
   instance directly and introduces no second definition of D(M). No extra notion is needed.
7. rg of all eight proposed declaration names in lean/Sheaf and the upstream names table:
   no existing definition of this helper or these theorems. Initial node-id search in
   dag/lean_names_upstream.json found no binding.

Edge cases checked mathematically: p=2; G trivial and the empty product; i the identity,
trivial subgroup, and full subgroup; q the identity and the terminal quotient; K=k;
imperfect k=F_p(t); M=0, M=Z, and M=Z/pZ. For the last case D(M)=μ_p is nonsmooth but
v(e_m)=e_m tensor 1 is still invertible, since the inverse raises coefficients to p and
multiplies by the second scalar. No inverse to coefficient Frobenius occurs. Pure-tensor
balancing was checked in both comparison formulas. Γ of an affine scheme and its field
extensions can have infinite vector-space dimension; no finite basis assumption is present.

Validation uses only the prescribed scompile.py wrapper, compiling the file both under a
sandbox name and its delivered module name. All theorem bodies remain `sorry`; no theorem
is proved. No STATEMENT-DISPUTED issue or node correction was found.

## Second reading by Q40

The same assigned worker reread the node, Milne source and Lean file; no additional agent
was started, as the dispatcher explicitly prohibits it. The maintainer performs the
independent review of the delivery. This reading caught that Lean drops unused section
hypotheses, so explicit `include` commands now retain commutativity and both finite-type
conditions on each participating group. It also checked the directions of the naturality
coordinate equation, the a^p b factor in field-extension θ versus a in the V formula,
the second-factor scalar in the product θ, and the counit formula for the zero group map.
All seven clauses above are present, including the nullary product and p-torsion M.
The diagonalizable conclusion identifies the equivalence with the canonical map on every
element, not merely on a chosen list of points. No statement change, new node, hidden
perfection assumption or unbound implicit was found.
