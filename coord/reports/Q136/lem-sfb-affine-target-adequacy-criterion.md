## Worker report

The module `Sheaf.AlgebraicGeometry.AffineTargetAdequacyCriterion` states
`CategoryTheory.adequatelyAffine_iff_global_power_lifting`. Its only theorem proof
is `sorry`; no definitions, axioms, helper theorems or new DAG nodes are introduced.
The original node is preserved except for `lean`.

Clause-by-clause correspondence:

- A field k is `{k : Type u} [Field k]`; the arbitrary commutative k-algebra is
  `(A : Type u) [CommRing A] [Algebra k A]`. In particular A can be the zero ring.
- The stack over k is `U : BasedCategory.{v,w} (Over (Spec (.of k)))`, with
  `hU : IsAlgebraicModuliStack U`. Object and morphism universes `v,w` are independent.
- The target is the discrete representable groupoid
  `discreteModuli (yoneda.obj (Over.mk (Spec.map
  (CommRingCat.ofHom (algebraMap k A)))))`. It is literally Spec A over Spec k.
  The morphism is `f : BasedFunctor U` to that groupoid.
- Quasi-compactness is `_hqc : IsQuasiCompactAlgebraicModuliMap` at exactly the
  universes used by `IsAdequatelyAffineMorphism`, with zero auxiliary enlargement;
  quasi-separatedness is `_hqs : IsQuasiSeparatedAlgebraicModuliMap f`.
- The left side is `∃ hY, IsAdequatelyAffineMorphism f hU hY`.
  The recorded definition takes a proof of target algebraicity even though its
  body never uses that proof. Existentially binding that proof avoids requiring
  any extra hypothesis. A scheme is an algebraic stack: Yoneda descent, a
  representable diagonal, and its identity smooth surjective scheme atlas.
  Thus the existential packages a canonical ambient fact, and does not assume
  a chosen atlas or strengthen the mathematical adequate-affineness condition.
- “If and only if” is `↔`, not merely an implication.
- Every pair of quasi-coherent O_U-algebras is quantified by
  `∀ (B C : ModuliAlgebraSheaf U hU.1.1)` followed by the two
  `IsQuasicoherentModuliAlgebra` premises. Their morphism is `q : B ⟶ C`;
  `IsSurjectiveModuliAlgebra q` is the dependency's local fppf lifting predicate,
  rather than objectwise or global surjectivity.
- Each target section is `∀ t : moduliGlobalSectionsRing C.right`.
  A single global positive exponent and a single global source section are
  `∃ N : ℕ, 0 < N ∧ ∃ s : moduliGlobalSectionsRing B.right`.
- The image equation is
  `∀ x : U.objᵒᵖ, (q.right.hom.app x) (s.1 x) = (t.1 x) ^ N`.
  Both sides are compatible families. Equality at every object is exactly equality
  of global sections, and pointwise powers are the recorded section-ring powers.
- There is no structural-ring comparison assumption, finite generation condition,
  Noetherian hypothesis, or characteristic restriction.

Dependency interfaces read in full:

- `Mathlib.Algebra.Field.Defs`, `Field`: the recorded Mathlib match for
  `def-weil-field`, giving a nontrivial commutative division ring.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map`:
  the recorded affine spectrum and its contravariant scheme map.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`,
  `CategoryTheory.IsAlgebraicModuliStack`: etale stack, algebraic-space diagonal,
  and existence of a smooth surjective scheme atlas.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`,
  `CategoryTheory.IsQuasiCompactAlgebraicModuliMap` and
  `CategoryTheory.IsQuasiSeparatedAlgebraicModuliMap`: the actual base-change and
  relative-diagonal predicates, reused without redefinition.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`,
  `ModuliAlgebraSheaf`, `IsQuasicoherentModuliAlgebra`,
  `IsSurjectiveModuliAlgebra`, and `moduliGlobalSectionsRing`: respectively
  algebras under the regular-functions sheaf, the general-site module predicate,
  fppf-local lifting, and compatible section families with pointwise operations.
- `Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism`,
  `CategoryTheory.IsAdequatelyAffineMorphism`: the qcqs plus arbitrary-algebra
  universally adequate direct-image condition. Its public import also exposes
  the preceding statement dependencies and the `discreteModuli` construction
  from `StablePointedModuliGroupoids`.

Proof dependencies with recorded interfaces are imported privately:
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit` (finite affine etale
refinement), `Mathlib.AlgebraicGeometry.Limits` (finite spectrum coproduct),
`Mathlib.RingTheory.Smooth.Flat` (etale implies flat),
`Mathlib.RingTheory.Flat.Basic` (finite direct-sum flatness),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` (flat and surjective spectrum
implies faithfully flat, and tensor-unit injectivity), and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness` (tensor right exactness).
The proof-only nodes `lem-sfb-algebraic-stack-fibre-products`,
`lem-sfb-stack-flat-scalar-sections`, and
`lem-sfb-stack-affine-algebra-direct-image` currently have no recorded modules,
so they have no imports. Their roles are explicitly retained in the theorem's
five-step proof docstring; they are not needed to type the statement.

Edge cases checked before writing: the empty affine scheme (A the zero ring)
and empty source stack are allowed; the unique sections there lift at N=1.
Zero algebra sheaves are included. The identity surjection admits N=1 and s=t.
Positive characteristic is allowed with arbitrary positive N; N=0 is excluded.
No boundedness or finite generation of the algebras is imposed. The source
stack's universes are independent, and the target uses the existing representable
universe convention (morphisms u, objects u+1).

Searches (2026-10-24):

- `msearch.py ... leanfinder` with the plain-language statement “A quasi compact
  quasi separated morphism from an algebraic stack to an affine scheme is
  adequately affine iff positive powers of global sections lift along every
  surjection of quasi coherent algebras”: eight hits on scheme affineness and
  affine-target morphism properties; no algebraic-stack adequacy criterion.
- `msearch.py ... loogle '"IsAdequatelyAffineMorphism", "moduliGlobalSections"'`:
  zero hits.
- `msearch.py ... grep 'AdequatelyAffine|adequately.affine|ModuliAlgebra|moduliGlobalSections'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and the upstream names index for
  the node id, `AdequatelyAffine`, `adequatelyAffine_iff`, and global power lifting:
  only the existing adequate-affineness definition, adequate-moduli definition,
  and unrelated ring/representation power-lifting results. None states this iff.
- The prescribed example module has been withdrawn (it contains no declarations);
  its node now points to `WeilConjectures.CategoryTheory.CompactObject`. That
  upstream module was read for the current header/docstring conventions.

Source check: the primary PDF https://arxiv.org/pdf/1005.2398v3 was opened and
Remark 4.1.3 and Lemma 4.1.8(2),(3) read. The HTML endpoint failed, but the PDF
was available. These give precisely the affine-base equivalence with adequate
(not necessarily universally adequate) global-section ring maps for all algebra
surjections. No statement correction or STATEMENT-DISPUTED flag is needed.

## Second reading by Q136

The dispatcher brief prohibits starting another agent and assigns independent
review to the maintainer. This section records a separate self-audit, not a claim
that another worker reviewed the delivery. I reopened the node and module and
checked the field, k-algebra, specified affine target, source algebraicity, both
qcqs premises, both directions of the iff, both quasi-coherence conditions,
local surjectivity, every target global section, positive exponent, source global
section, and the componentwise image equation. No clause was changed or omitted.
The proof of algebraicity of the representable target is existentially closed
in the conclusion rather than introduced as an extra premise. There are no new
nodes or dependency modules. The independent maintainer review remains required.

Validation: `scompile.py Q136 lem-sfb-affine-target-adequacy-criterion` compiled
both sandbox and library module names cleanly (4.5 and 3.9 seconds in the explicit
final compile). `deliver2.py ... --no-push` returned OK: the delivery passes the
server preflight and per-file compile, with no errors or unexpected warnings.
