## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_supported_constant_presentation` in its
original module, with its original signature and all three public definitions unchanged.
Consolidated the earlier attempt's six files into this module; the added constructions
and lemmas are private proof helpers, with no new public interface or module.

The proof constructs the fixed-scalar sheaf of continuous functions to the discrete
coefficient ring, proves the constant-function comparison locally bijective, and checks
that it intertwines the specified constant restriction. Ambient open neighbourhoods of
fibres on the closed subspace prove local surjectivity. Complementary-range vanishing
proves the zero composite. The existing open-extension monicity criterion, together
with local lifting on zero and nonzero open fibres, identifies the open counit with
the kernel. Transport through the existing intrinsic realization and normalized
rank-one isomorphisms gives the desired kernel fork. Finally
`Abelian.epiIsCokernelOfKernel` gives the exact displayed cokernel cofork.

Updated the item's node proof, proof dependencies and proof origin to this argument.
The unit record `sk-prop-a1-kummer` has no realized statement or steps bypassed here;
this is a change only below the unit level. All original public imports are retained.
The additional imports are private proof dependencies from Mathlib and the already
proved source-library open-extension interfaces. Import-direction checks passed for
Mono, Complement and Conservative.

Validation: `lcompile.py` compiled the complete consolidated module without errors or
warnings in 7.2 seconds. No direct Lean/Lake invocation or shared-repository edit was
made. Empty schemes, an empty or total closed subscheme, disconnected objects and the
zero ring are included: the empty-cover local-injectivity case and zero-fibre lift
are explicit, and neither geometric case requires an inhabited point or a nonzero scalar.

The resumed dry run compiled the complete module and passed the axiom probe, then
requested a change record for the balanced private proof scopes. Added
`coord/changes/R3-supported-constant-private-proof-scopes.md`, recording the exact
unchanged theorem signature and all 206 transitive consumers. No consumer adaptation
is needed: all public definitions, signatures and public imports are unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.proEtale_supported_constant_presentation`
(node `lem-pur-proetale-supported-constant-presentation`).

Holes closed: 1. Holes added: 0. Holes split off: 0. Sorries remaining in the item or
added elsewhere by this delivery: none. The private zero-composite, epimorphism,
constant-function comparison and kernel lemmas are all proved in this module.
This is a proof from the published dependency interfaces; it does not claim to remove
holes already present in intrinsic coefficient realization or its normalized comparisons.

## No longer needed

Removed these original proof-only imports:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections`

The intrinsic extension interface remains available through its original public
adjunction import; no separate proof import is needed. Ordinary module sheafification
is not used: the proof works with fixed-scalar sheafification and transports its result
through the existing equivalence.

Removed these proof-dependency edges from the item's node:

- `lem-pur-proetale-finite-constant-sections`: its ring-valued comparison is replaced
  by the proved private fixed-scalar module-valued comparison, normalized at the unit.
- `lem-weil-pbc-affine-scheme-qcqs`: the ambient open neighbourhoods already form a
  Zariski cover; affine reduction and finite subcover selection are unnecessary.
- `lem-weil-pbc-closed-immersion-base-change`: the proof uses Mathlib's existing
  closed-immersion pullback instance and closed-embedding theorem directly.
- `lem-weil-proetale-weakly-etale-localization`: the existing concrete localization
  and open-factorization API suffices; the large packaged localization theorem is unused.
  Its obsolete top-level tool approval is withdrawn in the node copy.
- `def-weil-presheaf-modules-sheafification`: no intrinsic module-sheafification
  universal property is used; ordinary sheafification and coefficient realization suffice.

No blanket claim is made that these nodes are unused by other parents. There are no
new helper modules to retain from the earlier sandbox: Defs, Zero, Epi, Kernel and
ConstantFunctions were never delivered and are consolidated here, not withdrawn from
the shared library. No `deleted.txt` is needed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had an unproved kernel placeholder, no node/change records for
its auxiliary modules, and a main proof that unpacked the zero equality as a pair.
It also moved the original public definitions to another module. This delivery fixes
the proofs and restores the definitions in their original module verbatim, removing
that extraction and its consumer/change-record obligations.

The node's planned explicit inverse from the kernel is unnecessary. It suffices to
prove its factorization locally surjective and monic, then use the abelian-category
isomorphism criterion. The existing open counit monicity and invertibility after open
restriction provide the needed injectivity and local lifts. Similarly the finite
coefficient hypothesis is retained exactly, although the private function comparison
and local lifting arguments do not themselves need finiteness.

The earlier transport failures are resolved in this session: the required initial dry
run reached the compiler and supplied actual diagnostics. All resulting type/coercion,
naturality and kernel-transport errors were repaired and the full file compiled.

The resumed preflight conservatively counts the added balanced namespace/section and
section-variable commands as an interface change, despite private declarations and
unchanged public definitions. The change record documents this for independent review.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
