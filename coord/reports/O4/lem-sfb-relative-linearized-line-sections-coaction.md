## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeLinearizedLineSectionsCoaction` states
`AlgebraicGeometry.RelativeLinearizedLineSections.exists_normalized_coaction`.
Its only theorem proof is `sorry`. The six auxiliary declarations contain real
constructions or abbreviations: the Laurent algebra, the existing Hopf-spectrum
torus, restriction of scalars on actual global sections, normalized section
pullback, the pullback of the given linearization, and evaluation of Laurent
coefficients by actual scheme morphisms. They are helpers for this node's
coaction statement, not replacement geometric hypotheses or additional objects
chosen from existence assertions.

Source read: `literature/stacks-project/coherent.tex`,
`lemma-flat-base-change-cohomology`, Tag 02KH, especially its degree-zero
canonical map for arbitrary flat ring maps (not merely field extensions).
The item is the explicitly agent-formulated consequence of that lemma and the
linearization identities, as its source record says. Its seven proof steps are
included in the theorem docstring. No statement correction is needed.

Hypothesis and clause correspondence:

- **Commutative ring A, S = Spec A:** `(A : Type u) [CommRing A]`,
  `X : Over (Spec (.of A))`. `X.hom` is precisely the given f, not a map selected
  later. There is no field, normality or Noetherianity assumption.
- **Rank r >= 0 and C = A[t_1^±1,...,t_r^±1]:** `(r : ℕ)` and
  `Coordinate A r = AddMonoidAlgebra A (ULift (Fin r → ℤ))`. The harmless lift
  puts the character lattice in A's universe. Its basis element t^m is
  `AddMonoidAlgebra.single (ULift.up m) 1`. Multiplication, comultiplication,
  counit and antipode are the canonical existing group-algebra structures.
- **T = Spec C with that group law:** `torus A r` abbreviates the recorded
  `ringDiagonalizableGroup A (ULift (Fin r → ℤ))`. This is directly the Hopf
  spectrum over A, without transport through Γ(S,O_S) or a field restriction.
- **Separated finite-type f:** `[IsSeparated X.hom]`,
  `[LocallyOfFiniteType X.hom]`, `[QuasiCompact X.hom]`. The last two are the
  recorded finite-type conjunction. No properness is imposed.
- **S-action with unit and associativity:** `[ModObj (torus A r).X X]` is the
  existing internal action in `Over S`. Its tensor product is the chosen
  scheme fibre product. `EquivariantCoherent.source` is its second projection;
  `target` is the action. `D : ActionGroupoidModel ...` is its presentation
  with the existing identity and inverse maps. Its `group_coordinate` pins
  composition to (g,h,x) ↦ (gh,x) on every test scheme, so no auxiliary groupoid
  law or extra restriction on the action is assumed. This is the same
  presentation interface used by `exists_normal_line_bundle_tensorPow_linearization`.
- **Invertible L:** `(L : X.left.Modules) [L.IsInvertible]` is exactly the
  recorded local rank-one predicate. Coherence or finite presentation of L
  is not added; on non-Noetherian rings it would be an unwarranted restriction.
- **Forward linearization theta: p^*L ≅ a^*L:** the binder `theta` has exactly
  that direction with `Scheme.groupoidModulePullback`, which is the recorded
  tensor pullback with an opaque interface. `hunit` and `hcocycle` are the
  recorded, canonically compared sheaf-map equations for its inverse. Inverting
  their equations is precisely the node's forward unit and cocycle convention.
  They are not equalities just at points.
- **V = Γ(X,L) with the structural A-action:** `sections A X L` is the
  evaluation `Γ(L,⊤)` restricted along
  `A → Γ(Spec A,O) → Γ(X,O)`; its underlying additive group is the actual group
  of global sections. There is no freeness or finite-generation assumption.
- **A-linear c: V → V tensor_A C:** the existential `c` is a Lean `LinearMap`
  into `sections A X L ⊗[A] Coordinate A r`.
- **Coassociativity:** the first conjunct compares `(c tensor id)(c s)`,
  transported by `TensorProduct.assoc`, with `TensorProduct.map id Coalgebra.comul (c s)`
  for every s. It uses the canonical Laurent coproduct, not an unspecified map.
- **Counitality:** the second conjunct applies `TensorProduct.map id Coalgebra.counit`
  and then `TensorProduct.rid`, and requires the result to equal s.
- **Normalization for every B and g, as equality of sheaf sections:** the third
  conjunct is its equivalent universal pullback form. For every test scheme W/S,
  `j : W ⟶ T ⊗ X` represents (g,x). For every finite tensor presentation
  `c s = ∑ i, v i ⊗ f i`, it asserts
  `∑ i, f_i(g) • (gx)^*v_i = theta_(g,x)(x^*s)`
  as global sections of the actual module `(gx)^*L` on W. `pullSection` is the
  tensor-adjunction unit and `thetaAt` is pullback of the actual sheaf map using
  the uniquely section-normalized composition isomorphisms. `coefficientAt` is
  pullback of the function f_i along the group coordinate. Thus the sum is the
  canonical comparison applied to the evaluation of c, independent of the
  chosen finite presentation. Every tensor has a finite presentation, so this
  is a full normalization, not a condition only on pure tensors.

  To recover the node's formula literally, take W = X_B over S, let p_B be its
  projection to X, pull g back from Spec B to W, and set
  `j = (g, p_B ∘ alpha_(g^-1))`. Its source is `p_B ∘ alpha_(g^-1)` and its
  target is p_B by the action identities. The displayed equality is then
  `beta_B((id tensor ev_g)c(s)) = theta_(g,g^-1 x)(s_B(g^-1 x))` in Γ(W,L_B).
  Conversely the node's normalization at the universal point over C gives the
  universal sheaf-section equality, and pulling it back along j gives the
  Lean conjunct on arbitrary W. No stronger mathematical claim is introduced.
  This explicit universal test-scheme form includes all A-algebras represented
  in the scheme universe, with arbitrary nilpotents and without flatness.
- **Evaluation of t^m:** `coefficientAt` pulls the function corresponding under
  `ΓSpecIso` to the basis element `single (ULift.up m) 1` along g. This is
  exactly the group-algebra evaluation `ev_g(t^m) = ∏ν g_ν^(m_ν)`, since a map
  from the Laurent spectrum is specified by those invertible coordinates.
- **Weight consequence:** the fourth conjunct explicitly specializes
  `c s = s ⊗ t^m` to `theta_(g,x)(x^*s) = ev_g(t^m) • (gx)^*s` on every W.
  The same substitution x = g^-1 y is precisely
  `g·s_B = ev_g(t^m) s_B`. Its direction is consistent with the downstream
  projective-embedding node's sign `s(gx)=g^(-m)theta_(g,x)s(x)`.
- **No nonflat base-change isomorphism:** no conclusion asserts invertibility,
  injectivity or surjectivity of V tensor B → Γ(X_B,L_B). The normalization is
  expressed by its canonical finite-sum section formula only. The proof uses
  invertibility only at C and C tensor C, which are free over A.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its `Hom`,
  `Spec` and `Spec.map`; local-affine scheme and contravariant actual spectrum.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`; the existing
  `Over S` cartesian monoidal product uses these chosen scheme pullbacks.
- `def-weil-pbc-scheme-conventions` fixes no additional declaration; its
  separated and finite-type conventions are rendered by Mathlib's classes.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, local rank-one condition.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`,
  `tensorPullbackSectionComp`; canonical tensor pullback normalized on 1 tensor s.
  The unit definition in `pullSection` is followed by restriction from f^-1(top)
  to top, so its output really is a global section.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup`, arbitrary-ring Laurent Hopf spectrum.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentGZero`:
  `source`, `target`, `identityArrow`, `ActionGroupoidModel`, `pullbackIso` in
  `AlgebraicGeometry.EquivariantCoherent`. Only the groupoid presentation and
  tensor-pullback interface are used; no coherent full-subcategory is imposed.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidModule`:
  `Scheme.groupoidModulePullback`, `groupoidModuleUnitLaw`,
  `groupoidModuleCocycleLaw`; these spell out the canonical sheaf-map laws.

The last three already-landed definition nodes were added to `stmt_deps`, as
permitted by the standing brief's rule for adding landed definition nodes. No
new node or dependency module was needed. Their transitive dependency paths
were checked from the JSON records and none reaches this item.

The stated proof dependency modules are imported without `public`, including
`EulerChar` for the current `lem-pc-flat-base-change-cohom` record. That record's
`finrankH_pullback` is only a field-extension dimension statement, not the
arbitrary-ring section isomorphism required by the accepted natural-language
proof. It is not used as a stronger hypothesis or substituted into the present
statement. Stage 3 will need the actual Tag 02KH degree-zero comparison interface
when proving this node. All statement dependencies have usable declarations;
no missing theorem is hidden in a data definition here.

Edge cases checked before drafting and again against the final signature:
rank zero uses the one-element character lattice; empty X and zero A are
allowed, with zero global sections and no nonempty assumption; empty finite
presentations (n = 0) are allowed; zero sections and infinite or torsion section
modules are included; arbitrary characteristic, zero divisors, and nilpotents
in A or B are allowed. The normalization stays an equality of module-sheaf
sections under arbitrary pullback. No pointwise detection, reducedness,
connectedness, finite-dimensionality or choice of a basis of V is used.

Searches actually run (through `msearch.py O4` for the external services):

- LeanFinder: `Global sections of a torus linearized invertible sheaf have a
  Laurent Hopf algebra coaction normalized by inverse action pullback`.
  Eight hits, principally Laurent Hopf algebra structure and generator laws,
  plus ordinary representation linearization; no relative section theorem.
- Loogle: `"AlgebraicGeometry", "coaction"`. Zero hits.
- Mathlib grep: `coaction|[Cc]omodule|lineariz.*[Ss]ection`, subdirectory
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: `Linearization of a sheaf for a group scheme action as an
  isomorphism between action and projection pullbacks with a cocycle`.
  Eight hits, ordinary free-module representation linearizations; no exact match.
- Project `rg` for linearizations, torus section coactions and this item's id in
  `lean/WeilConjectures` and `lean/Sheaf`: found the field-only
  `GroupSchemeLinearization.Linearization`, affine Hopf-coaction equivalence,
  projective section-algebra action, and the downstream projective-embedding
  proof citation. None states this result for arbitrary A and arbitrary V.
  The existing arbitrary-base action-groupoid and ring-diagonalizable-group
  modules are reused. A final search for the proposed namespace and theorem
  name found no existing declarations.

Validation: the prescribed `scompile.py` server wrapper compiled the module
both as a sandbox file and under its delivered module name, without errors or
unexpected warnings. Both auto-implicit options are disabled; all universes
and section variables are explicitly declared. Every delivered theorem has
only `sorry` for its proof. All Lean lines have at most 100 characters.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
