## Worker report

The module `Sheaf.AlgebraicGeometry.TameSmoothRepresentationChart` states
`AlgebraicGeometry.exists_tame_smooth_representation_chart`, with `sorry` as its
entire proof. It introduces no definitions, auxiliary axioms, or additional nodes.
The item's natural statement, proof, and dependencies are unchanged.

Hypotheses and conclusion, clause by clause:

- The exponent is the positive integer `N`, with `hN : 0 < N`. This makes explicit
  the positive root-of-unity index implicit in the statement and explicit in the
  source and the proof's group-algebra lemma. `G : Type v`, `[Group G]`, `[Finite G]`
  and `hG : ∀ g, g ^ N = 1` give exactly the finite group of exponent dividing N.
- `ζ : ℂ` and `hζ : IsPrimitiveRoot ζ N` specify a primitive complex root as in the
  source. `A : Subalgebra ℤ ℂ` and
  `hA : A = Algebra.adjoin ℤ {ζ, (N : ℂ)⁻¹}` specify precisely Z[1/N,ζ].
  This subalgebra contains the integers through its prescribed integer algebra
  structure. No cyclotomic field or arbitrary coefficient ring substitutes for it.
- `(p : Ideal A) [p.IsPrime]`, `[Algebra A Λ]` and
  `[IsLocalization.AtPrime Λ p]` specify the prime localization Λ. The class is
  Mathlib's universal-property encoding of localization, allowing any isomorphic
  carrier of that exact ring. `Λ : Type u` need not have the small universe of A.
- `X B : Scheme.{u}` with `[IsLocallyNoetherian X]` and
  `[IsLocallyNoetherian B]` are the two locally Noetherian schemes. The structure
  map on B is `b`; the structure map on X is `h ≫ b`. Thus every input morphism h
  is a morphism of the stated Λ-schemes, without an extra unrelated structure map.
  `[Smooth h]` is the recorded smooth-morphism definition.
- `aX : G →* Aut X`, `aB : G →* Aut B` are actual group actions, including their
  laws. `hb` says B's action is over Spec Λ, so the action on Λ is trivial.
  `hh` states equivariance of h. It also implies that X's action is over Λ.
- `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, and `x : Spec (.of Ω) ⟶ X`
  are a geometric point in the project's established scheme-universe convention.
  `hx : ∀ g, x ≫ (aX g).hom = x` fixes the geometric morphism itself, including
  residue fields; it does not merely fix its underlying topological point.
- `X'`, `B'`, `i`, `j`, `h'`, `x'`, `aX'`, `aB'` give equivariant pointed étale
  neighborhoods of source and base. `Etale i`, `Etale j`, `x' ≫ i = x`, and
  `h' ≫ j = i ≫ h` record the neighborhood maps and the square. The lifted base
  point is `x' ≫ h'`; the square implies that it maps to `x ≫ h`.
  The next three universal equalities state equivariance of i, j, and h'. The last
  equality fixes x' geometrically. Thus the neighborhoods themselves are pointed
  equivariant neighborhoods of the original fixed point and its image.
- The module is `(V : ModuleCat.{u} Λ)` with
  `(n : ℕ) (_ : Module.Basis (Fin n) Λ V)`: an actual finite free module, with
  all finite ranks permitted. `ρ : Representation Λ G V` is a Λ-linear action;
  since G is a group, every `ρ g` is invertible with inverse `ρ g⁻¹`.
- `c` has codomain `pullback (j ≫ b) (Spec.map (CommRingCat.ofHom
  (algebraMap Λ (SymmetricAlgebra Λ V))))`. This is the exact stated fibre
  product over Spec Λ with the actual symmetric algebra, not an independently
  chosen algebra or a polynomial surrogate. Mathlib's SymmetricAlgebra has the
  universal linear-generator presentation specified in the node.
- `Etale c` is the recorded étaleness predicate. `c ≫ pullback.fst _ _ = h'`
  makes it a B'-morphism, with the required projection.
- The last universal equality is the second projection of equivariance of c.
  Its first projection is precisely equivariance of h', already included. Since
  the pullback projections are jointly monic, these two equations are exactly
  equivariance for the diagonal action. On the second factor the g-map is
  `Spec.map` of the algebra extension of `v ↦ ρ g⁻¹ v`, using
  `SymmetricAlgebra.lift ((SymmetricAlgebra.ι Λ V).comp (ρ g⁻¹))`.
  This inverse is essential: Spec is contravariant, whereas Aut and Representation
  use left actions. It is exactly the inverse-pullback convention recorded in
  proof Step 3. No arbitrary comparison map is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`, the affine-local smooth class recorded by
  def-sbc-smooth-morphisms; its definition and the recorded source equivalence
  with the infinitesimal-lifting definition were checked.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
  `AlgebraicGeometry.Etale`, the class recorded by def-weil-etale-morphism.
  Its affine-local ring-map signature and the node's match were read.
- For the proof route the module privately imports
  `Sheaf.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree` and
  `WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree`. These provide
  `Scheme.Hom.isFiniteLocallyFree_relativeDifferentials`,
  `Scheme.Hom.relativeDifferentials`, and
  `Algebra.Etale.iff_exists_squareJacobianPresentation`, with the latter also
  importing `Algebra.SquareJacobianPresentation`.
  The Mathlib imports transitively provide `Smooth.exists_isStandardSmooth`,
  `Algebra.SubmersivePresentation.basisKaehler`, and
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff`.
  All their recorded source signatures/docstrings were read. The proof-only node
  lem-per-local-cyclotomic-group-algebra-split has neither a Lean record nor a
  Mathlib match, so it has no module to import. Its use remains explicitly named
  in the six-step proof docstring. No unproved dependency is added as a hypothesis.

Edge cases checked before writing:

- Rank zero is allowed by `n = 0`; the zero module has the empty basis and symmetric
  algebra Λ, so the assertion reduces to étaleness near the point.
- G trivial and N=1 are allowed; ζ=1 and A=Z, and the assertion is the ordinary
  pointed smooth-chart theorem.
- The prime p may be zero: characteristic-zero generic coefficient localizations
  are included. Nonzero primes exclude exactly characteristics dividing N since
  1/N belongs to A. No positive characteristic or closed-point hypothesis is added.
- X or B empty has no input x, so the assertion is correctly vacuous. Neighborhoods
  cannot be made empty because x' must map to x.
- Nonclosed points are allowed, and no identification of relative differentials
  with a maximal-ideal quotient is used in the docstring. The proof follows the
  node's repaired differential-generator argument.
- Base actions can be nontrivial: only their map to Spec Λ is invariant. Neither
  h nor the action on X is assumed faithful, separated, affine, or of constant rank.
- No independent small universe for schemes/testing points is introduced; G's
  universe v is independent, and Λ, V, Ω and schemes use the established universe u.

Source read: ILO PDF, printed pp.137--140 (PDF pages 143--146), particularly the
second-assertion argument on p.138 and coefficient localization on p.139. The
node's reviewed proof avoids the source's closed-point/radicial reduction and
works with differentials of local functions; the Lean docstring follows all six
steps of that reviewed proof. No statement correction or dispute is needed.

Searches for an existing declaration (raw msearch results are in searches.jsonl):

- msearch leanfinder: "finite group equivariant etale coordinates smooth morphism
  at fixed geometric point symmetric algebra representation" returned eight hits,
  headed by `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
  and ring-level standard-smooth/étale presentation results. None gives equivariant
  scheme coordinates or a lifted integral representation.
- msearch leansearch: "equivariant etale local linearization smooth morphism finite
  tame group fixed geometric point" returned eight hits: representation
  linearization formulas, Etale, Scheme.Etale and smoothness/finite-presentation
  consequences, with no matching equivariant-chart theorem.
- msearch loogle: `SymmetricAlgebra.map, Representation, CyclotomicRing` returned
  zero hits with an unknown-identifier note for SymmetricAlgebra.map. Follow-up
  `"SymmetricAlgebra", "Representation"` completed normally with zero hits.
- msearch grep: `equivariant|[Cc]yclotomic|IsPrimitiveRoot` in Mathlib
  AlgebraicGeometry returned zero hits. Direct rg searches of Mathlib, upstream
  WeilConjectures and side Sheaf for `exists_tame_smooth_representation_chart`,
  `tame_smooth_representation`, and `equivariant.*etale.*chart` found no match.
  Upstream grep for this exact blueprint id also found no match.
- Broader rg searches of upstream and Sheaf for group actions, primitive roots,
  cyclotomic rings and symmetric algebras found the Mathlib notions used here,
  log-scheme action definitions, and the existing Gabber fixed-locus chart. The
  latter is a downstream log-chart theorem, not this smooth representation chart.
  The DAG and upstream-name index contain no existing declaration of this item.

Validation: scompile.py compiled the delivered file cleanly in both sandbox and
library-name modes (2.4 s and 2.7 s), with no warnings. Every theorem proof is sorry.

## Second reading by Q108

No second reading by a worker: under the direct-delivery brief, the maintainer's
independent review reads this delivery. No independent reading is claimed here.
