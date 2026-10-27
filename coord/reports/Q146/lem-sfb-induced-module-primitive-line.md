## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.InducedModulePrimitiveLine` states
`AlgebraicGeometry.induced_module_primitive_line`, with one `sorry` and no proved
result. Its two fully constructed helper declarations belong to this node:
`RhoSection.inducedCharacterModule` specializes the existing actual section subspace
at the inverse character and exponent one, and `RhoSection.inducedFixedSpace` is its
intersection with the kernels of the universal left-translation fixedness equations.
No independent notion has been invented and no new definition node is needed.

Source read: Milne, Algebraic Groups (2017), Definition 22.21 and Proposition 22.22,
printed pp.468--469, extracted from PDF pages 480--481. The definition has
f(xb)=f(x)lambda(b inverse); the proposition states the unique primitive line and
its weight w0(lambda). The whole five-step accepted DAG proof is in the theorem
docstring. The T times U decomposition and longest element use the stated sources
21.72--21.74 and the accepted DAG proof. No statement correction or dispute.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The Field and IsAlgClosed declarations and their docstrings were read in Mathlib.
- S, T, B and U are `Grp (Over (Spec (.of F)))`: exactly group objects among
  F-schemes, using the recorded `CategoryTheory.GrpObj` notion, with bundled
  group-scheme homomorphisms. No affine instance or dimensional restriction is added.
- Semisimplicity is `hS : IsSemisimpleGroupScheme S.X`, the definition used by
  the recorded rho-section theorem: smooth, connected, affine, finite type, and
  no nontrivial smooth connected solvable normal closed subgroup.
- Simply connected is exactly the `hsc` signature of the recorded
  `exists_rho_section_modules`: every semisimple S', every group-scheme map f,
  surjectivity, finite kernel and centrality after every F-algebra extension imply
  `IsIso f`. Finite kernel is `IsFinite (GrpObj.ker f).hom`; over a field this
  is finite-dimensionality of its coordinate algebra. The centrality equality
  quantifies over every kernel point x and S'-point s, as in that dependency.
- The split maximal torus, Borel, and containment are the same dependency's
  `hpair : IsRhoBorelPair iT iB k`, including `k ≫ iB = iT`.
- The radical U is expressed by `hUclosed`, `hUnormal`, `hUsmooth`,
  `hUconnected`, `hUunipotent`, and `hUmax`. The last says that every smooth
  connected normal closed unipotent subgroup of B factors through iU. This is
  precisely the largest-subgroup universal property in the landed Borel-pair
  structure module; no choice of a different subgroup is allowed.
- The actual conjugation action on B is `a : ModObj T.X B.X` pinned by `ha`.
  This is data specifying the action already mentioned in the node, not a new
  assumption on the group. The positive roots are `RankOneRoots.roots T B a`,
  exactly the nontrivial character weights on Lie(B), using the recorded tangent
  weight spaces. No abstract or Lie-algebra differential root system is substituted.
- The character of B is `lam : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)`.
  Its trivial restriction to U is `hlam : iU.hom.hom ≫ lam.hom.hom = 1`.
  Its restriction to T is composition `k ≫ lam`.
- Multiplication T times U to B is the first conclusion:
  `IsIso ((fst T.X U.X ≫ k.hom.hom) * (snd T.X U.X ≫ iU.hom.hom))`.
  It is an isomorphism of F-schemes, not a claim that this order's product map
  preserves the direct-product group law. Thus unique factorization holds on
  every test algebra.
- `w0 : RankOneRoots.Weyl iT` is in the actual normalizer quotient N(F)/T(F).
  `n0 : RankOneRoots.normalizer iT` is a representative and the equality
  `QuotientGroup.mk n0 = w0` records this. Normalizing is tested over all algebras.
- `e : T ≅ T` is fixed by the displayed equality with conjugation by n0 inverse
  on the inclusion iT. Consequently the character action is precomposition by
  e.hom, i.e. chi(n0 inverse t n0). It is not an arbitrary automorphism.
- The image equality of `RankOneRoots.roots T B a` under `e.hom ≫ chi` with
  its image under `chi⁻¹` is exactly w0(Phi+) = -Phi+. The longest element and
  T times U isomorphism are concluded independently of E being nonzero.
- The actual E_B(lambda) is `inducedCharacterModule S B iB lam`, definitionally
  `sectionModule S B iB lam⁻¹ 1`. The latter already imposes the stated right
  equivariance on regular functions over every commutative F-algebra. Pointwise
  inversion of the character supplies lambda(b) inverse, and exponent one
  leaves that coefficient unchanged.
- E nonzero is `inducedCharacterModule S B iB lam ≠ ⊥`. Only the primitive-line
  conclusion is conditional on this, exactly as in the node.
- The fixed subspace is `inducedFixedSpace`: it contains precisely f in E for
  which `evaluate ((x ≫ iU ≫ iB)⁻¹ * g) f = evaluate g f` for every A, x and g.
  This is the left-translation fixedness identity. These are full scheme
  identities: evaluate on the universal pair over F[U] tensor F[S] to recover
  the coaction identity. Conversely that coaction identity specializes to every
  such equation. It does not merely test F-points, smooth reduced tests or Lie
  algebra fixedness, and introduces no independent coaction choice.
- One-dimensionality is `Module.finrank F (inducedFixedSpace ...) = 1`, which
  also entails finiteness (Mathlib finrank is zero in the infinite-dimensional
  case). No finite-dimensionality assumption on E has been made.
- The character action on the entire fixed line is the final equality for every
  f in that subspace and every A, t and g. Its left side is f(t inverse g).
  Its coefficient is `characterValue (t ≫ e.hom ≫ k ≫ lam)`, exactly
  lambda(n0 inverse t n0)=w0(lambda)(t), with no additional inverse. Universal
  evaluation recovers the weight coaction identity. Since scalar extensions are
  generated by these f, the equality is also the asserted action on the
  scalar-extended line, including at nilpotent algebra points.

Dependency declarations used and read:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically closed
  clause of def-weil-algebraic-closure; no algebraic closure is chosen here).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, and its
  Cartesian functor-of-points group operations. The recorded group-scheme
  explanation in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` was read.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`: `AlgebraicGeometry.IsRhoBorelPair`,
  `AlgebraicGeometry.exists_rho_section_modules` (the latter's exact hsc
  interface is reused, rather than the result being assumed).
- `Sheaf.AlgebraicGeometry.RhoSectionModuleData`: `RhoSection.Coordinate`,
  `RhoSection.evaluate`, `RhoSection.characterValue`, `RhoSection.sectionModule`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `RankOneRoots.roots`, `RankOneRoots.normalizer`, `RankOneRoots.Weyl`, with
  their recorded point-image, torus denominator and tangent weight definitions.
- `Sheaf.AlgebraicGeometry.TrivialTorusCoherentData`:
  `TrivialTorusCoherent.multiplicativeCommMonObj`, the already recorded
  commutativity instance which permits character inversion. None of its
  coherent-module data is restated here.
- For the proof plan, the imports are the recorded modules for
  `reductive_borel_pair_structure`, `Scheme.Hom.image`,
  `IsSchemeTheoreticallyDominant.of_isDominant`, `Smooth.geometricallyReduced`,
  and `eq_zero_of_forall_algHom_apply_eq_zero`. Their signatures and docstrings
  were read. There is no declaration yet for the proof dependencies
  lem-sfb-longest-weyl-open-cell, lem-sfb-comodule-finite-subrepresentation,
  or lem-sfb-unipotent-rational-representation-fixed-vector, so no import for
  these is possible. They are retained in the proof and proof_deps.

The item's stmt_deps gains only three already landed terminology nodes:
def-sfb-rank-one-root-interfaces, def-sfb-rho-section-module-data and
 def-sfb-trivial-torus-coherent-data. This uses brief-stage2 section 5's
permission to add landed nodes needed for the statement. Their entire statements,
Lean records, and the declarations actually used were read. No dependency node
is changed. The main statement, proof, proof_deps, and all other node fields stay
unchanged.

Edge cases checked before writing: the trivial semisimple group and rank-zero
split torus have empty positive roots, trivial Weyl group, E=F and its full
one-dimensional fixed space. No positive rank or nonempty root set is assumed.
If E=0 the conditional imposes no false line claim. If lambda is trivial the
formula has coefficient one. The inverse sign matches Milne's convention;
for E_B(-m rho) it gives the expected w0(-m rho)=m rho. Arbitrary positive
characteristic, including characteristic two, is allowed: character inversion
is in the character group, not division or negation in the base field.
Nonreduced algebras and the zero algebra are included. The test-algebra universe
is the same u as the scheme's coordinates; universal coordinate algebras and
their finite tensor products lie in it, so this testing determines the full
scheme identities and excludes no larger scalar-extension identity.

Searches made with the prescribed msearch wrapper:

- leanfinder: "A nonzero induced module of a Borel character of a semisimple
  algebraic group has a one dimensional unipotent fixed subspace of longest Weyl
  weight". Eight hits, all LieModule/LieAlgebra results (for example
  LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero and
  LieModule.Weight.genWeightSpace_ne_bot), not this group-scheme statement.
- loogle: "Representation.invariants, Module.finrank". Two hits, abstract
  finite-group character averaging results, not regular-function induction.
- grep: "induced.*module|primitive.*line|highest.*weight" in
  Mathlib/RepresentationTheory. Two unrelated coinduction/category hits.
- rg of the upstream WeilConjectures and project Sheaf sources for
  inducedCharacterModule, inducedFixedSpace, induced_module_primitive_line,
  the item id and primitive-line/induction variants: no existing matching
  declaration. The existing RhoSection module was found and reused.
- Read related SimpleModuleDualHighestWeight and RationalHighestWeightData:
  those require a separately supplied coaction on a simple rational module;
  they do not supply the induced regular-function subspace and canonical
  left action needed here. Its abstract invariants definition therefore does
  not replace the explicit universal function equalizer without supplying that
  additional coaction and its scalar-structure transport. The final construction
  stays directly in the recorded RhoSection coordinate algebra instead.

Validation: every compile uses scompile.py. The first draft exposed a mismatch
between scalar structures on two existing coordinate-algebra APIs; the final
statement uses only the RhoSection evaluation API for functions. A clean compile
of the final statement is recorded by the wrapper; no #check commands, hidden
implicit variables, private notation, local instances, or non-sorry theorem proofs
are left.

## Second reading by Q146

A separate pass by this worker re-read the node, source text, final module and
all imported statement interfaces under the dispatcher's instruction not to start
other agents. Independent review remains the maintainer's. In this pass the
unnecessary IsAffine binders on S, T and U were removed: they were implied by the
geometric hypotheses and the final evaluation-based formulation needs none of
them. The sign was rechecked twice: sectionModule at lam inverse gives the
right-equivariance coefficient lam(b) inverse; e is conjugation by n0 inverse,
so the final character is w0(lam), with no opposite or dual. The first conclusion
is an isomorphism in Over, not in Grp. The root-reversal and decomposition clauses
are outside the E-nonzero implication. The fixedness equalizer tests all algebras
and functions at all points, not only rational points. Finrank one rules out both
the zero subspace and an infinite-dimensional fixed space. All variables and
universes are explicit and the only theorem proof is sorry. No remaining
statement mismatch or source error was found.
