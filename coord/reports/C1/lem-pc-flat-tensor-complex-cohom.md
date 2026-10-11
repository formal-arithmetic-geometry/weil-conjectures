## Worker report

The node is already stated by Mathlib's canonical homology comparison.  No module is
added.  The declaration is `CategoryTheory.ShortComplex.mapHomologyIso` in
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`:

```
noncomputable def mapHomologyIso [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homology ≅ F.obj S.homology
```

For the node's hypotheses, take `A` and `B` to be the commutative rings with
`[Algebra A B]` and `[Module.Flat A B]`; these encode the flat ring map.  Take
`C : CochainComplex (ModuleCat.{u} A) ℤ`, and `i : ℤ`.  The functor is
`F = tensorRight (ModuleCat.of A B)`, so `F.obj C.homology` is
`Hⁱ(C) ⊗_A B`, while `(C.sc i).map F).homology` is the homology of the
tensorized short complex, definitionally `Hⁱ(C ⊗_A B)`.  Thus the inverse of
this canonical iso has exactly the direction in the node.  The node also binds
`_hC : ∃ a b : ℤ, C.IsStrictlyGE a ∧ C.IsStrictlyLE b`; this boundedness input is
accepted by the node but is not needed by the general Mathlib comparison.

The required preservation instances are Mathlib's
`Module.Flat.instPreservesFiniteLimitsTensorRight`-style instance
`[Module.Flat R M] : PreservesFiniteLimits (tensorRight M)` from
`Mathlib.RingTheory.Flat.CategoryTheory`, finite-colimit preservation of the
left adjoint `tensorRight M` from `Mathlib.CategoryTheory.Monoidal.Closed.Braided`,
and the resulting `(tensorRight (ModuleCat.of A B)).PreservesHomology` instance.
`mapHomologyIso` itself is in
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` (around line 455).

Dependency declarations used: `def-weil-pbc-flat-ring-map` supplies the flat
ring-map interpretation (`Algebra A B` and `Module.Flat A B`); `def-pc-cochain-
complex-modules` supplies `CochainComplex`; both are used through their recorded
Mathlib declarations.

Edge cases checked: every integer degree, including zero and negative degrees;
zero and empty complexes; inverted or empty bounds; zero rings; and no finite
nonempty index, Noetherian, finite-generation, or characteristic hypothesis.
The generic Mathlib iso has no boundedness requirement.

Searches for an existing declaration:

- LeanFinder (`msearch.py C1 lem-pc-flat-tensor-complex-cohom leanfinder
  "extension of scalars commutes with cohomology of a complex"`): found the
  general homology-preservation infrastructure, including `ShortComplex.mapHomologyIso`.
- Loogle (`... loogle "CategoryTheory.ShortComplex.mapHomologyIso"`): found
  `CategoryTheory.ShortComplex.mapHomologyIso` and its preservation hypotheses.
- Grep of Mathlib: `mapHomologyIso` occurs in
  `Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`; the flat tensor
  instance occurs in `Mathlib/RingTheory/Flat/CategoryTheory.lean` (the
  `PreservesFiniteLimits (tensorRight M)` instance at line 90), and the tensor
  left-adjoint finite-colimit facts are in
  `Mathlib/CategoryTheory/Monoidal/Closed/Braided.lean`.
- Grep of the project and upstream `WeilConjectures`: no competing declaration
  for this statement; the only relevant existing declaration is the Mathlib one.

No `STATEMENT-DISPUTED` or node fault remains.

## Earlier second reading (a previous round; superseded)

Re-read the node, its dependency records, and the Mathlib declarations.  The
Mathlib declaration is the canonical comparison `(S.map F).homology ≅ F.obj
S.homology`; applying it to `F = tensorRight (ModuleCat.of A B)` and `S = C.sc i`
provides the exact isomorphism claimed by the node.  `Algebra A B` and
`Module.Flat A B` supply the flat map, the cochain complex and every integer
cohomological degree are bound explicitly, and the boundedness hypothesis is
present even though the general theorem does not use it.  No mismatch was found.

## Second reading by C1

The node introduces a flat homomorphism (A\to B), a bounded cochain complex (C^\bullet) of (A)-modules, and an integer (i), and concludes that the canonical comparison (H^i(C)\otimes_A B\to H^i(C\otimes_A B)) is an isomorphism. The recorded Mathlib declaration `CategoryTheory.ShortComplex.mapHomologyIso` renders the canonical homology comparison for the short complex in degree (i), with tensor extension represented by `tensorRight`; its hypotheses are preservation of homology, supplied by flatness. The boundedness hypothesis is retained by the node but is not needed by this general comparison.

Edge cases include every integer degree (including zero and negative degrees), zero and empty complexes, zero rings, and vacuous or inverted bounds; no finite index, Noetherian, finite-generation, or characteristic assumptions are introduced. Searches of Mathlib, the project, and upstream found no more specialized declaration. No mismatch was found in the recorded abstraction.
