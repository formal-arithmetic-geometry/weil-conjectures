## Worker report

The delivery states `AlgebraicGeometry.affineGroupoid_basis_descent` in
`Sheaf.AlgebraicGeometry.AffineGroupoidBasisDescent`, with its sole proof `sorry`.
It also supplies the missing notion of groupoid laws for specified scheme maps,
`AlgebraicGeometry.IsGroupoidScheme`, as a fully written Prop-valued structure in
`Sheaf.AlgebraicGeometry.GroupoidScheme`. The item statement is unchanged; its
statement dependencies gain only the new definition node. No theorem is proved,
no data is chosen from an existence theorem, and no additional hypotheses are imposed.

The previous attempt had confused NZ's merged **stage-1** split with a stage-2
statement. The current shared node has the NZ split review, but no `lean` record.
The preserved sandbox had no module, node copy or report. This delivery supplies
that missing stage-2 work.

Correspondence for every hypothesis and conclusion of the item:

- Commutative rings A and B are the bundled arguments `A B : CommRingCat.{u}`;
  U and R are literally `Spec A` and `Spec B`. No nonzero, domain, reduced,
  Noetherian or field assumption is made.
- The five maps are the arguments `s t`, `e`, `i`, and
  `c : pullback s t ⟶ Spec B`, with exactly the domains in the node.
- The functorial groupoid condition is `_hG : IsGroupoidScheme s t e i c`.
  All identity, inverse, source/target and associativity laws are included, as
  detailed below. They concern the given morphisms, not unrelated pointwise choices.
- Sigma and tau are `(Spec.preimage s).hom` and `(Spec.preimage t).hom`.
  `Spec.preimage` is the inverse of `Spec.map` on affine schemes, so these are
  exactly the ring homomorphisms s-sharp and t-sharp after the canonical
  identification of the global sections of a spectrum with its ring.
- C is exactly `RingHom.eqLocus (Spec.preimage s).hom (Spec.preimage t).hom`.
  Its carrier is the set of a with sigma(a) = tau(a). The scalar structure on A
  is Mathlib's algebra over a subring, whose algebra map is the inclusion.
- The positive finite rank is `r : ℕ` with `_hr : 1 ≤ r`.
  The elements are `x : Fin r → A`; indexing from zero instead of one just labels
  the same r vectors. In particular the intended finite nonempty case is retained.
- The basis hypothesis is literally its unique-expression formulation in the
  node: `_hbasis : ∀ b : B, ∃! a : Fin r → A,
  b = ∑ j, sigma (a j) * tau (x j)`. The multiplication explicitly specifies
  the sigma action on B; there is no ambiguous global choice of an A-algebra
  structure on B. Finiteness makes all coordinate families finitely supported.
- The first conclusion is `∃ b : Module.Basis (Fin r) C A, ∀ j, b j = x j`.
  It requires these particular elements to be the C-basis, rather than merely
  asserting freeness or existence of some basis.
- The second conclusion is a ring equivalence `f : (A ⊗[C] A) ≃+* B`, together
  with `∀ a a₂, f (a ⊗ₜ a₂) = sigma a * tau a₂`. This specifies the exact
  canonical comparison, uniquely on the generating pure tensors. Existence of
  this characterized ring equivalence is exactly that this canonical ring map
  is an isomorphism. It is not an uncharacterized `Nonempty` isomorphism or an
  arbitrary map substituted for the canonical construction.

All six proof steps of the node are carried in the theorem docstring, with the
node ids used in each. In particular the two A-actions in the intermediate
B tensor B are distinguished, the coefficient ring in step 3 is the second B,
and the comparison has the stated order sigma(a) tau(a₂).

Dependency declarations read and used (including the proof-only plan imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (the scheme and affine-spectrum definition nodes).
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage` and
  `Spec.homEquiv`, the canonical correspondence giving s-sharp and t-sharp.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`; imported through
  `Mathlib.AlgebraicGeometry.Pullbacks`, which supplies their scheme instances.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`; its basis notion is
  `Module.Basis` from `Mathlib.LinearAlgebra.Basis.Defs`. The node explicitly
  defines a basis by unique expansion, used verbatim for the hypothesis and by
  the existing bundled basis for the conclusion. No private basis definition.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` / `.Basic`: `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift`, and `TensorProduct.ext'`, read for
  the module-tensor definition node; supplied through the ring-tensor import.
- `Mathlib.AlgebraicGeometry.Pullbacks`: `pullbackSpecIso` and its two projection
  formulas, the recorded affine-fibre-product proof leaf.
- `Mathlib.LinearAlgebra.TensorProduct.Basis`: `Module.Basis.baseChange` and
  `baseChange_apply`, the recorded base-change-of-free-modules proof leaf.
- `Mathlib.RingTheory.TensorProduct.Basic` / `.Maps`:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `productMap`, `productMap_apply_tmul`, `ext`, the recorded
  tensor-ring universal-property proof leaf.
- `Mathlib.Algebra.Ring.Subring.Basic`: `RingHom.eqLocus`, with carrier exactly
  the specified equality locus; `Mathlib.Algebra.Algebra.Basic`:
  `Subsemiring.ofSubsemiring` and `algebraMap_ofSubring`, the existing inclusion
  scalar structure. These are provided by the ring-tensor imports.

Every statement dependency has a usable existing Mathlib interface. No dependency
record was repaired and no duplicate notion was introduced for them. The
proof-only imports are retained as required by stage 2.

Edge cases checked before writing:

- A = 0: the identity section forces B = 0 too. The invariant subring and tensor
  ring are zero. Positive-size bases over the zero ring are valid, and every
  coefficient function in the unique-expression hypothesis is the sole such
  function. No `Nontrivial` instance excludes this case.
- R empty but U nonempty cannot have the assumed identity map. This is correctly
  ruled out by the actual groupoid hypothesis rather than an added nonemptiness.
- Rank one for the identity groupoid gives the standard unit-generator basis
  statement; zero rank is excluded by the node's explicit r >= 1.
- For the pair groupoid of k × k over k, the two idempotents give C = diagonal k;
  the sigma/tau and composition orientation agree with the indicated tensor map.
- The pair groupoid of k[epsilon]/(epsilon²) over k with basis 1,epsilon is also
  covered. No independence argument divides by a coefficient or uses reducedness.
- Test schemes live in the same universe as U and R, so U, R, their pullbacks
  and the triple pullbacks needed to witness the laws are included. There is no
  independently smaller test universe making the hypothesis vacuous. Scheme-map
  equations and Yoneda imply the corresponding laws for larger test schemes too.

Searches made using `msearch.py` and source searches (all real results):

- LeanFinder: "For an affine groupoid, a basis given by target images descends
  to the invariant ring and the canonical tensor comparison is an isomorphism".
  Eight hits: Kaehler tensor comparisons, representation-theoretic free modules,
  algebra presentations and a tensor-product fan. None has groupoid invariants
  or this descent assertion.
- LeanSearch: "A groupoid scheme consists of schemes of objects and arrows with
  source target identity inverse and associative composition". Eight hits, mainly
  `CategoryTheory.Groupoid`, constructors and `Scheme.instCategory`. They describe
  ordinary groupoids, not laws on prescribed scheme morphisms.
- Loogle: `"Groupoid", "Scheme"`: no hits. An earlier exploratory query involving
  `CategoryTheory.GroupoidObject` reported that identifier unknown; that is not
  treated as independent evidence of mathematical absence.
- Mathlib grep: `GroupoidScheme|IsSchemeGroupoid|groupoid.*basis|basis.*groupoid`:
  no hits. An additional `GroupoidObject` spelling also gave none.
- `rg` over upstream `WeilConjectures/` and side `lean/Sheaf/` for groupoid
  objects/schemes, a groupoid basis theorem, the item id and the proposed names:
  no matching groupoid-scheme interface or basis-descent declaration. The only
  broader groupoid-object hit is the Segal-space notion in
  `Sheaf.CategoryTheory.SpaceGeometricDescent`, which takes a simplicial space
  functor and does not describe these scheme maps.
- DAG search for groupoid-scheme definitions found the related affine-groupoid
  statements, not a definition node. `tools/blueprint_refs.py search 'groupoid
  scheme'` returned group-variety/isogeny statements and effective descent,
  not this notion. `ancestor` gives `lem-a1-affine-hc0`.

Sources opened: the entire statement and proof of Stacks 03C8 in `groupoids.tex`,
its explicit groupoid axioms, Definition 0231 and the following septuple
characterization. The result is the finite nonempty instance of that source.
No statement dispute, source correction or unit-statement change is needed.

Validation: the prescribed `scompile.py` compiled both delivered modules separately,
in dependency order, including the private overlay and library-form checks. All
checks were clean (about 1.6–1.8 seconds each), with no errors or unexpected warnings.
The delivery dry run and final delivery are performed after this report is written.

## New nodes

`def-a1-groupoid-scheme` defines the full groupoid laws for the five given scheme
morphisms. Its source is Stacks 0231 and the explicit axioms immediately preceding
it. It has its own module and is added to the item's statement dependencies. It
uses the existing scheme and fibre-product definition nodes. The LeanSearch,
Loogle, Mathlib grep, project grep, DAG and blueprint searches above found no
existing node or declaration for this scheme-valued notion. Ordinary
`CategoryTheory.Groupoid` cannot directly express the external source/target maps
on the prescribed arrow scheme; the new definition supplies this absent interface.

For completeness, correspondence of every clause of the new definition:
`identity_source` and `identity_target` give se = te = id;
`inverse_source` and `inverse_target` give si = t and ti = s;
`composition_source` and `composition_target` give sc = s pr1 and tc = t pr0.
For each test H and a : H → R, `identity_comp` and `comp_identity` give the two
unit laws; `inverse_comp` and `comp_inverse` give the two inverse laws, with
outputs e(s(a)) and e(t(a)) in that order. `associative` gives c(c(a,b),d) =
c(a,c(b,d)) for every triple with s(a) = t(b) and s(b) = t(d).
All compositions into the pullback use Mathlib's actual `pullback.lift`.
The extra proof binders in those fields are compatibility proofs for that lift,
not extra hypotheses on a groupoid: the first six laws ensure they exist for
all the indicated arrows, and proof irrelevance makes the result independent
of which proof is supplied. Naturality is inherited from morphism composition
and uniqueness of the pullback lift. No groupoid data, proof field or construction
contains `sorry`; only the intended theorem above does.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
