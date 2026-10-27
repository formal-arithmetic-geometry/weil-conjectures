## Worker report

The delivery states `AlgebraicGeometry.normal_big_cell_character_functions` in
`Sheaf.AlgebraicGeometry.GroupScheme.NormalBigCellCharacterFunctions`. This is stage 2:
the sole theorem has proof `sorry`. Four auxiliary definitions belonging to this
statement contain actual data: `NormalBigCell.chart`, `value`, `chartFunction`, and
`leftCoaction`. No definitions or dependency interfaces are replaced. No statement
correction or mathematical dispute was needed.

Sources read: Milne, Algebraic Groups (2017), printed pp.468–471, especially Definition
22.21, the proof of Proposition 22.22, and Lemmas 22.23–22.25. The current blueprint unit
is `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`;
its direct-images proof supplies the alteration-reduction ancestor recorded by this
node. This is an auxiliary statement, not the unit's own statement. The normality
assembly and universal-algebra extension of the identities follow the accepted DAG
proof, whose seven steps are copied as a detailed natural-language proof plan into
the theorem's docstring.

Hypotheses, matched to Lean:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The four actual group schemes are `H T B U : Grp (Over (Spec (.of F)))`.
  `hH : ReductiveTorusCentralizer.IsReductive H` is the recorded smooth connected
  affine finite-type reductive-group predicate, with geometric unipotent radical
  triviality. Over an algebraically closed base it gives exactly the node's notion.
- `iT`, `hT : ...IsMaximalTorus iT` and `hsplit` give the specified split maximal torus.
  `iB`, `hB : IsBorelGroupScheme iB.hom.hom`, `j`, and `hj : j ≫ iB = iT`
  express the specified Borel containing this torus, including its actual inclusion.
- `iU` and `hU` specify the unipotent radical as a smooth connected normal closed
  unipotent subgroup containing every such subgroup; this is precisely the radical
  interface of `reductive_borel_pair_structure`, rather than an arbitrary subgroup.
- `p : B ⟶ T`, `hp : j ≫ p = 𝟙 T`, and `hker : IsPullback ...` specify the
  group-homomorphic projection, its identity restriction on T and its kernel U.
- `aB`, `haB` pin the action on Lie(B) to conjugation. `Φplus` and `hΦplus`
  identify the positive roots as exactly its nontrivial character weights. This
  uses the recorded tangent-character weight spaces, including in positive
  characteristic. Coroots and a base are not additional hypotheses: they are
  supplied by the Borel-pair theorem and do not occur in any asserted formula.
- `n₀ : RankOneRoots.normalizer iT` is the specified rational normalizer point.
  Its class in the recorded normalizer quotient is w₀. `s : Aut T` together with
  `hs` specifies its conjugation morphism on every test scheme. `hlong` says
  exactly that inverse-conjugation pullback sends the positive characters to
  their negatives. Thus the specified representative has class w₀, and s is
  not an arbitrary automorphism or unspecified Weyl action. The separate symbol
  w₀ is eliminated by using the representative's actual conjugation everywhere.

Conclusions, matched to Lean:

- `IsOpenImmersion (NormalBigCell.chart iU iB n₀.val).left` and `DenseRange ...`
  are the specified multiplication map and its dense open image. The definition
  of `chart` is literally `(u,b) ↦ u n₀ b` using products of scheme-valued maps.
- The existential `IsIntegral H.X.left` and `IsAffine H.X.left` expose the
  derived geometric properties, rather than assuming them. The explicit
  `Nonempty (⊤ : H.X.left.Opens)` witness is a conclusion needed by the generic
  germ API; it follows from integrality and excludes no case of the hypotheses.
- `IsDomain Γ(H.X.left, ⊤)`, `IsIntegrallyClosed ...`, and `IsFractionRing ...
  H.X.left.functionField` express the normal coordinate domain and its stated
  fraction field. `Scheme.functionField` is precisely the generic stalk.
- `Function.Injective (H.X.left.germToFunctionField ⊤)` embeds R into F(H).
  `C`, its nonemptiness, `e : (U.X ⊗ B.X).left ≅ C.toScheme`, and the equation
  `e.hom ≫ C.ι = chart.left` identify C with the entire chart image. The second
  injective germ map embeds Γ(C,O) into the same function field. The restriction
  embedding R→Γ(C,O) follows too, since its composite is the first injective germ
  map. There is no independently chosen embedding or fraction field.
- `f : Character T → Γ(H.X.left,C)ˣ` gives the invertible regular functions.
  Their pullback along e is required to equal `chartFunction p s χ`, the actual
  pullback of the Laurent coordinate through the inverse of `(w₀χ)p` on the
  B-coordinate. `C.topIso.inv` is the canonical identification of sections on C
  with global sections of its open subscheme. Thus these are the precise
  character functions, not units satisfying an unrelated existential property.
- The next clause states that their images in F(H) are nonzero.
- For χ, ψ, ξ with `ξ.hom.hom = χ.hom.hom * ψ.hom.hom`, the equality
  `f ξ = f χ * f ψ` is f_(χ+ψ)=f_χ f_ψ in multiplicative character notation.
  The witness ξ means the pointwise product character; it is not an additional
  restriction on the characters. This avoids requiring a separate commutativity
  instance on the target merely to spell the addition of two characters.
- The extension premise is equality of the germs of a global section r and
  f_χ in the specified function field. For every `A : CommAlgCat.{u} F`, u,t,g,b
  are respectively U(A), T(A), H(A), B(A). The three equalities are exactly
  r(u inverse g)=r(g), r(t inverse g)=χ(t)r(g), and
  r(gb)=((w₀χ)(p(b))) inverse r(g). Inverses are taken in G_m before evaluation,
  so A may be nonreduced or the zero ring; no division operation on A is assumed.
  All four point variables can be quantified together because every group of
  points has its identity; no identity becomes vacuous from an empty point type.
- For every χ, the existential submodule E is characterized by membership iff
  the last right-equivariance identity holds over every algebra. It is exactly
  E_B(w₀χ), including when it is zero, not a chosen larger module.
- Its coaction δ is pinned by
  `(E.subtype.rTensor R) ∘ₗ δ = leftCoaction H ∘ₗ E.subtype`.
  `leftCoaction` is explicitly `(1 tensor S) flip Delta`, with the canonical
  coordinate Hopf structure; it evaluates to f(a inverse g). The existing
  `HopfAction.Coassociative` and `Counital` predicates impose both rational
  coaction identities. The final implication places every regular extension r
  of f_χ in this same E. Neither finite dimensionality nor a weaker action only
  on F-points is substituted for rationality.

Dependency declarations used:

- `Field`, `IsAlgClosed`, and `CategoryTheory.GrpObj` are the existing Mathlib
  notions recorded by the field, algebraic-closure and group-scheme nodes.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` supplies the exact Borel-pair
  interface used above; its dependency definitions provide reductivity, maximal
  tori, Borels, unipotence and tangent-character weights.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `RankOneRoots.Character`, `normalizer`, `Weyl`, `multiplicativeValue`.
  The landed owning node `def-sfb-rank-one-root-interfaces` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `RationalHighestWeight.coordinateOverGroup` and `coordinateHopf` expose the
  actual canonical coordinate Hopf structure on the bundled group. Its landed
  owning node `def-sfb-rational-highest-weight-data` is added to stmt_deps.
  `HopfAction.Coassociative` and `Counital` come from its public imports.
- `WeilConjectures.AlgebraicGeometry.FunctionField` imports the recorded integral
  scheme function field `Scheme.functionField` and `germToFunctionField` from
  Mathlib; no component-product replacement is made for the integral group H.
- Proof-only imports cover `bruhat_longest_cell_charts`, `IsRegular.of_smooth`,
  `regular_normal_and_normal_decomposition`, `Scheme.exists_germToFunctionField_eq`,
  and `pullbackSpecIso`, using their recorded modules. Mathlib FunctionField also
  supplies `functionField_isFractionRing_of_isAffineOpen`, germ injectivity and
  the fraction-field-of-stalk instance. The Hopf result is the canonical Mathlib
  Group/Affine instance brought by the public coaction imports; the standard
  group schemes are imported through the existing public interfaces.
- `lem-sfb-longest-weyl-open-cell` has no recorded module in the read DAG, so
  there is no proof-only import for it. Its statement is already a clause of
  the imported Bruhat theorem; it supplies no missing statement-level notion.

Edge cases checked before finalization:

- Trivial group: Φplus is empty, all charts are the identity of Spec F, and the
  sole character function is 1. Every existential and every action law is valid.
- Torus/rank zero: U=1, B=H=T, s is the identity, n₀ can be any torus point;
  f_χ(g)=χ(n₀)χ(g) inverse, so it is globally regular and has left weight χ.
- Zero character gives the constant unit 1; the multiplicative law includes it.
- SL₂ with the upper triangular Borel and n₀=[[0,-1],[1,0]]: for the character
  diag(t,t inverse)↦t^m, f_χ is c^m on the cell c≠0, where c is the lower-left
  coordinate. Left multiplication by diag(t inverse,t) scales it by t^m.
  For m<0 it need not extend, correctly leaving the global identities conditional.
- Characteristic p is unrestricted; weights are characters, not derivatives.
  Test algebras include F[ε]/ε² and the zero algebra, and the formulas use unit
  evaluation rather than a fictitious inverse on a general ring.
- No positive-rank, nontrivial-character or nonzero-E hypothesis is added.
  All universes and implicit variables are explicitly bound (`autoImplicit false`).

Searches actually run:

1. `msearch.py ... leanfinder "The coordinate ring of a reductive group is normal
   and torus characters define invertible regular functions on the open Bruhat cell"`:
   eight hits, on Lie/root representations, finite-group characters and the abstract
   left regular representation; none states this scheme-level result.
2. `msearch.py ... loogle "Scheme.functionField, IsIntegrallyClosed"`: zero hits,
   with `unknown identifier 'Scheme.functionField'` reported by the service. This
   is not taken as evidence that the Mathlib notion is absent: its local source
   was opened and reused.
3. `msearch.py ... grep "Bruhat|bigCell|big_cell|characterFunction" AlgebraicGeometry`:
   zero Mathlib hits.
4. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
   `bigCell|big_cell|characterFunction`, and separately for `NormalBigCell` and the
   proposed theorem name found no duplicate. Broader rational-representation
   searches found the existing coaction and highest-weight interfaces used here.
   Full signatures and docstrings of the statement dependencies, their relevant
   terminology, and recorded proof inputs were read rather than inferred by name.

Validation: `scompile.py N9 lem-sfb-normal-big-cell-character-functions <module>`
compiled the sandbox and the exact delivery module successfully, with no errors
or non-sorry warnings (reported compiler times 9.9 s and 10.6 s). The initial
compile exposed the need to make nonemptiness of the top open explicit for the
function-field germ API; it is now a derived existential conclusion. No stronger
hypothesis was added. Delivery preflight is run after this report is written.

Delivery dry run: `deliver2.py N9 lem-sfb-normal-big-cell-character-functions --no-push`
reported OK: the packet passes the server preflight and compiles. The only changed
node fields are `lean` and the two added landed statement dependencies. The sole
sorry is the theorem above; the recorded signature matches its source verbatim,
and all Lean source lines have at most 100 characters.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
