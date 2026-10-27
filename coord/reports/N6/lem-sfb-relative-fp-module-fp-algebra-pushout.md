## Worker report

The module `Sheaf.RingTheory.RelativeFinitePresentationFpAlgebraFibreProduct` states
`Module.finitePresentation_relative_fpAlgebra_fibreProduct`, with proof `sorry`.
Source read: Stacks `more-algebra.tex`, Tag 08KP,
`lemma-relative-finitely-presented-module-over-fibre-product`, including its complete
polynomial-reduction paragraph, and Situations 08KH and 08KK. The statement agrees
with hypotheses (1)-(3) of that lemma after renaming the ambient algebra to D and
the intermediate flat algebra to E. No node correction or new definition is needed.

Hypotheses and clauses, in order:

- Commutative rings A, A', B: separate `Type uA`, `Type uA'`, `Type uB` binders and
  three `CommRing` instances. The maps are `f : B →+* A`, `g : A' →+* A`, and
  `hg : Function.Surjective g` is precisely the required surjectivity.
- The ring R is Mathlib's `f.pullback g`, whose elements are pairs `(b,a')`
  satisfying `f b = g a'`, with its subring operations. `hB`, `hA'`, `hA` fix
  the component algebra maps to the two projections and their common composite.
  These are explicit specifications of the node's given canonical actions.
- D is a commutative R-algebra: `(D : Type uD) [CommRing D]
  [Algebra (f.pullback g) D]`.
- The factorization R → E → D is `[Algebra R E] [Algebra E D]` together with
  `[IsScalarTower R E D]`, where R denotes `f.pullback g`. The tower says the
  given R → D map is the composite, rather than an unrelated algebra structure.
  `[Module.Flat R E]` and `[Algebra.FinitePresentation E D]` are exactly the two
  factorization conditions. E has its own independent universe `uE`.
- D_B, D_A', D_A are the actual `D ⊗[f.pullback g] B`, respectively A' and A.
  The right-factor component actions are fixed by `hDB`, `hDA'` on `1 ⊗ b`
  and `1 ⊗ a'`. The maps to D_A are fixed by `hBA`, `hA'A` on every pure tensor:
  `d ⊗ b ↦ d ⊗ f b` and `d ⊗ a' ↦ d ⊗ g a'`. Thus the supplied algebra
  structures are canonical, not arbitrary maps. Pure tensors generate, so the
  equations uniquely specify these actions; the towers specify their restriction.
- N is an additive group with `[Module D_B N]`,
  `[Module.FinitePresentation D_B N]` and `[Module.Flat B N]`. Its B and D
  actions are the restrictions along the canonical maps, expressed by the two
  `IsScalarTower` binders. These structures always exist for the node's N.
- M' is handled symmetrically by `[Module D_A' M']`,
  `[Module.FinitePresentation D_A' M']`, `[Module.Flat A' M']`, with the
  corresponding restriction towers. N and M' have independent universes.
- The gluing equivalence `φ` is D_A-linear from `D_A ⊗[D_B] N` to
  `D_A ⊗[D_A'] M'`. These are canonically the node's `N ⊗[B] A` and
  `M' ⊗[A'] A`. Explicitly, on the unprimed side the identification sends
  `(d ⊗ a) ⊗ n` to `(d • n) ⊗ a`; its inverse sends `n ⊗ a` to
  `(1 ⊗ a) ⊗ n`. The primed formulas replace B, N by A', M'.
  Balancedness follows from the specified right-factor actions. These inverse
  maps preserve the D_A-actions. Transporting the node's φ gives exactly this φ,
  with no additional condition on the gluing isomorphism.
- M is the target tensor module of φ. `TensorProduct.mk D_B D_A N 1` sends
  `n ↦ 1 ⊗ n`, which under the preceding identification is `n ↦ n ⊗ 1`;
  composing with φ gives the first gluing map. The primed `TensorProduct.mk`
  gives `m' ↦ m' ⊗ 1` under the primed identification.
- The argument of `Module.FinitePresentation D` is `LinearMap.ker` of the
  difference of those two maps after `LinearMap.fst` and `LinearMap.snd`.
  It consists exactly of `(n,m')` with equal overlap images. Its submodule
  structure restricts the product D-module structure, hence is the required
  coordinatewise action. This renders K and the whole finite-presentation conclusion.
- There is no `[Module.Flat R D]`, no ideal-finiteness or nilpotence condition,
  no Noetherian assumption, and no nonzero-ring or nonzero-module assumption.

Dependency declarations used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, equivalently the recorded
  `Module.Flat` from `Mathlib.RingTheory.Flat.Basic`, used for E, N and M'.
  Read the class and its tensor-injectivity interpretation in the source.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, used for
  D over E; read its full finite-polynomial-presentation signature and docstring.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` / `Basic`: `TensorProduct`,
  `TensorProduct.mk`, its pure-tensor formula and universal `TensorProduct.lift`.
  This is the `mathlib_match` of `def-weil-pbc-module-tensor-product`, which
  has no lean record and does not require one.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`,
  used on both component modules and on the conclusion; read its class signature.

The already recorded proof modules are imported privately, including
`Sheaf.RingTheory.RelativeFinitePresentationFibreProduct` with
`Module.finitePresentation_relative_fibreProduct` and
`Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation` with
`Module.finitePresentation_iff_of_finite_of_finitePresentation`. Both full
signatures and proof-plan docstrings were read. The former supplies the same
canonical-overlap encoding; its flatness assumption on the ambient algebra is
replaced here by the node's weaker flat-then-finitely-presented factorization.
Other proof imports provide MvPolynomial, projective-implies-flat,
`Module.Flat.trans`, and tensor right exactness. The docstring follows every
step of the node's proof, including generation of the base-changed kernels.

Edge cases checked before drafting: all rings may be zero; all modules may be
zero; f need not be surjective; g may be an isomorphism; the kernel of g may be
arbitrary; D may be nonflat over R; the polynomial presentation may have zero
variables or zero relations. None is excluded by any binder. For example one
can take identity base maps over the integers, E the integers, D the field of
two elements, and both modules zero: D is nonflat over R, yet all hypotheses
are meaningful. No relation among any of the seven universe parameters is
imposed. Extra action/tower binders express the given canonical structures,
which exist for every mathematical datum, rather than finiteness restrictions.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder` query: "Compatible relatively flat modules finitely
  presented over an algebra finitely presented over a flat algebra patch to a
  finitely presented module over a ring fibre product". Eight hits: finite-free
  factorization of maps into flat modules, finite-presentation transitivity and
  restriction, base change, and flatness restriction. None states this patching lemma.
- `msearch.py ... loogle` query: `Module.FinitePresentation, Module.Flat`.
  Six hits, including flat finite-presentation projectivity and finite-free
  factorization; none states relative patching.
- `msearch.py ... grep` query:
  `(fibre.?product|fiber.?product|Milnor|patch).*(FinitePresentation|finite.?present)|`
  `(FinitePresentation|finite.?present).*(fibre.?product|fiber.?product|Milnor|patch)`.
  Zero hits in Mathlib.
- `msearch.py ... leansearch` query: "Finite presentation of relatively flat
  modules glued over a surjective ring pullback with a finitely presented ambient
  algebra over a flat algebra". Eight hits: definitions of finite presentation,
  finite presentations as data, base change, and faithful-flat descent. No match.
- `rg -n 'finitePresentation_relative|relative.*[Ff]ibreProduct|`
  `lem-sfb-relative-fp-module-fp-algebra-pushout'` on `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: only the flat ambient-algebra
  theorem and an unrelated relative-dimension theorem. The item's ID has no
  source occurrence. The flat theorem requires D flat and is not an exact match.

Validation: `scompile.py N6 lem-sfb-relative-fp-module-fp-algebra-pushout` compiled
both sandbox and library module modes successfully, initially in 3.2 and 2.8 s.
All universes and variables are explicit; `set_option autoImplicit false` enforces
this. The sole postponed theorem has `sorry` and the complete node proof plan.
There are no statement disputes or dependency-interface faults.

## Second reading by N6

The dispatcher explicitly forbids starting another agent, and the maintainer supplies
an independent review of this delivery. This section records my own second reading,
not a claim of an independent worker review. I reopened the node, the Stacks source
and the complete theorem signature after compilation.

The check distinguished E from D: flatness is on E over R, algebra finite presentation
is on D over E, and the factorization is enforced by the scalar tower. It checked the
finite-presentation hypotheses are over D_B and D_A', while flatness is over B and A'.
The equations for the two overlap algebra maps are precisely induced by f and g;
the equivalence is linear over D_A. Expanding the two tensor identifications above
shows both maps in the kernel become exactly the two maps in the node. The kernel
has the product D-action and the conclusion is finite presentation over D itself.
I also checked no flatness of D, ideal hypothesis, Noetherian condition, or Nontrivial
instance slipped in. On this reading I renamed the right-factor action equations
from hSB/hSA' to hDB/hDA' to match D; no mathematical statement changed. All four
statement dependencies use their recorded Mathlib notions, without copied definitions.
