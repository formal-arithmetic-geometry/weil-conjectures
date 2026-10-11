## Worker report

The module states the derived tensor–Hom adjunction for a scheme `X`. It binds a scheme,
the derived-category instances on `X` and each open, perfect objects `A` and `I`, and an
arbitrary object `E`. The existential family `e` is a bijection between
`I ⟶ RHom(A,E)` and `A ⊗ I ⟶ E`; the final universal clause records naturality under
maps `f : A' ⟶ A`, `g : I' ⟶ I`, and `h : E ⟶ E'`. The perfectness hypotheses are retained
exactly as stated by the node, while `E` has no perfectness hypothesis.

The scheme is `X : Scheme.{u}` and the derived-category hypotheses are the two explicit
`HasDerivedCategory` binders. `schemeDerivedCategory X` renders `D(O_X)`; the shared global
instance `schemeDerivedTensorMonoidal` renders `⊗ᴸ` via notation `⊗`; and
`derivedInternalHom (Opens.grothendieckTopology X) X.sheaf` renders `RHom`. The maps in the
naturality equation are `f ⊗ₘ g` and the internal-Hom functor map `(f.op, h)`.

Dependencies used: `Sheaf.AlgebraicGeometry.PerfectComplex`, declaration
`AlgebraicGeometry.Scheme.IsPerfect`; `Sheaf.AlgebraicGeometry.DerivedCategory`, declaration
`AlgebraicGeometry.schemeDerivedCategory`; `Sheaf.AlgebraicGeometry.DerivedTensorStructure`,
declaration `AlgebraicGeometry.schemeDerivedTensorMonoidal`; and
`Sheaf.Algebra.Homology.DerivedInternalHom`, declaration `CategoryTheory.derivedInternalHom`.
The proof is `sorry`, as required for stage 2; its documented route applies
`lem-sc-derived-internal-hom-adjunction` in the symmetric form from Stacks Tags 08DJ and
0FPB, then evaluates the natural equivalence.

Edge cases checked: `E` is unrestricted, either perfect object may be zero, the category may
have no nontrivial morphisms, and the naturality quantifies arbitrary maps (including zero
maps and identities). No affine, nonempty, or characteristic hypothesis was added.

Searches: `msearch.py ... leanfinder "derived tensor Hom adjunction for perfect complexes of
sheaves of modules on a scheme"` returned only unrelated condensed-module closed structures;
`msearch.py ... loogle "CategoryTheory.Adjunction.homEquiv, CategoryTheory.MonoidalClosed"`
returned only generic monoidal-closed equivalence lemmas; grep of Mathlib and the source for
`derivedInternalHom|schemeDerivedTensor|tensorHomAdjunction` found no exact scheme statement.
The project search found no declaration for this blueprint node. Stacks Tag 08DJ states the
canonical derived internal-Hom isomorphism functorial in three objects, and Tag 0FPB supplies
the symmetric monoidal derived tensor structure.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the dry-run tool accepts this section's absence.

## Second reading by S1

I independently read the item node, its Lean module, all four statement-dependency
nodes and their recorded declarations, the shared derived-tensor node/module, and
`lem-sc-derived-internal-hom-adjunction` with its now-landed module.

Object, hypothesis and conclusion checklist:

1. A scheme X: `(X : Scheme.{u})` uses Mathlib's `Scheme`, the recorded
   declaration of `def-pc-scheme`. No affineness, separation, Noetherian,
   nonemptiness, base field or characteristic assumption occurs. Verdict: exact.
2. D(O_X): `schemeDerivedCategory X` is the recorded localization of all
   `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, not D_QCoh or an
   étale derived category. I opened DerivedCategory.lean and the `moduleRings`
   abbreviation: the latter is exactly `sheafCompose` of X's commutative
   structure sheaf with the forgetful functor to rings. Consequently it is
   definitionally the carrier used by `derivedInternalHom`. Verdict: exact.
3. Perfect A and I: `Scheme.IsPerfect X A` and `Scheme.IsPerfect X I` occur
   independently in the family e. I read PerfectComplex.lean: perfection is
   locally being represented by a bounded complex whose terms are summands
   of finite free modules. This is the dependency node's notion. Both
   `HasDerivedCategory.{w}` binders are the shared localization infrastructure
   required by D(O_X) and that definition on opens; they impose no additional
   geometric finiteness condition. Verdict: exact.
4. Arbitrary E: `∀ E : schemeDerivedCategory X`, without perfection,
   quasi-coherence or boundedness. Verdict: exact.
5. RHom(A,E): `(derivedInternalHom (Opens.grothendieckTopology X)
   X.sheaf).obj (op A, E)` uses the dependency's functor, not a private
   internal Hom. I read its construction: localize the Hom-complex bifunctor
   using the functorial K-injective replacement of the second variable.
   Verdict: exact, including contravariance in A.
6. A tensor^L I: `A ⊗ I` uses the global `schemeDerivedTensorMonoidal`.
   Its definition uses the K-flat derived monoidal construction of the
   recorded sheaf tensor. Thus it is the derived tensor on D(O_X), not
   an arbitrary monoidal tensor or the pro-étale coefficient tensor.
   Verdict: exact; no new tensor definition is needed.
7. Natural bijection: `∃ e : ∀ A I, IsPerfect X A → IsPerfect X I → ∀ E,
   (I ⟶ RHom(A,E)) ≃ (A ⊗ I ⟶ E)`. The single existential family supplies
   simultaneous choices before the naturality clause. Perfectness proofs
   are proof-irrelevant. An Equiv is precisely a bijection of these Hom sets.
   Verdict: exact.
8. Naturality in all three objects: for arbitrary `f : A' ⟶ A`,
   `g : I' ⟶ I`, `h : E ⟶ E'`, the input is
   `g ≫ t ≫ derivedInternalHom.map (f.op, h)` and the output is
   `(f ⊗ₘ g) ≫ e A I hA hI E t ≫ h`. I checked the types and order:
   both sides are maps A' tensor^L I' → E'. Taking two maps to be identities
   recovers each individual naturality condition. Primed A and I are
   perfect because the family is on the same perfect-object domains.
   Verdict: exact, no stronger closure assumption.
9. Correspondence of morphisms: applying the Equiv to arbitrary t gives
   the stated transpose A tensor^L I → E; its inverse gives the reverse
   correspondence. No missing clause or extra conjunct. Verdict: exact.

Source reading: the repository's literature checkout is absent on this
machine. I read the available local Stacks .tex checkout instead, including
perfect.tex's discussion of RHom and its reference to the internal-Hom
section of Cohomology. The node's primary locator `section-RHom` and
`cohomology-lemma-RHom-strictly-perfect` do not occur under those names in
this checkout; the precise supporting source is already recorded in the
node's proof: cohomology.tex, `section-internal-hom`, equation
`equation-internal-hom`, and `lemma-internal-hom` (08DJ), together with
`lemma-symmetric-monoidal-derived` (0FPB). I checked the tag map. The section
assumes only a ringed space; 08DJ is functorial in arbitrary K,L,M.
Substituting K=I, L=A, M=E and using tensor symmetry gives exactly the node.
There is no hidden affine or Noetherian hypothesis. No statement correction
is needed, and no unit statement is changed.

Edge cases: the empty scheme is allowed (the local perfection condition
is vacuous there, as it should be); either perfect object and arbitrary E
may be zero. Identity and zero maps are included by the unrestricted
naturality quantifiers. There is no index set or n parameter; in particular
no nonempty-index or n>0 restriction. No characteristic condition appears.
Both scheme/module universe u and localization Hom universe w remain
parameters, inherited from the dependency declarations; no field-only or
fixed-small-universe specialization is introduced. Every variable and
universe in the signature is explicitly bound.

Independent searches (different phrasing from the worker):

- LeanFinder: "internal Hom right adjoint to derived tensor product on
  ringed spaces" returned eight ordinary pullback/sheaf or light-condensed
  closed-category hits, none this derived scheme statement.
- Loogle queries `Adjunction.homEquiv` and
  `CategoryTheory.MonoidalClosed.homEquiv` reported unknown identifiers;
  these failed queries are not evidence of absence. A subsequent query
  `CategoryTheory.Adjunction` returned twelve generic adjunction declarations
  (identity, constructors, equivalence adjunctions and adjoint instances),
  none the derived scheme/perfect-object statement.
- LeanSearch: "For perfect complexes A and I on a scheme, morphisms from
  I to derived internal Hom of A and E correspond to morphisms from their
  derived tensor product to E." was unavailable (Internal Server Error);
  no absence verdict is inferred from this service failure.
- `rg` searched Mathlib's Homology and Monoidal directories, the source
  WeilConjectures tree and the project's Sheaf tree for `derivedInternalHom`,
  `tensorHomAdjunction`, derived Hom equivalences and perfect tensor-Hom
  combinations. I opened the relevant nearby declarations. Upstream
  `SheafOfModules.tensorHomEquiv` is for ordinary sheaves, and
  `AlgebraicGeometry.Etale.derivedTensorHomAdjunction` is for an étale sheaf
  derived category. Project `perfect_tensor_hom_duality` is QCoh duality,
  with no displayed RHom bijection. Project
  `scheme_derivedInternalHom_adjunction` is the node's broader proof tool:
  it states unrestricted objects, both tensor orders, and a symmetry,
  not this exact perfect-object statement. It supplies the docstring's
  proposed proof and requires no dependency repair. No exact duplicate
  statement or duplicated definition was found.

Standards and repairs: no mathematical mismatch was found, and the Lean
and node record are retained unchanged. The only addition is this independent
reading report. There are no new nodes or dependency modules in the delivery.
The module defines no data and has exactly one theorem, whose proof is
`sorry`. Its module and theorem docstrings carry the source and blueprint
identifier, and the theorem docstring follows both proof steps of the node,
including the correctly ordered substitution and tensor symmetry. Imports
are used, lines meet the 100-character limit, and there is no file-local
notation, private definition, local instance or hidden statement let-binder.
The node's `lean.statement` was compared verbatim (whitespace-normalized)
with the theorem signature. Local single-file compilation completed with
exit code 0 and no warnings. Final server compilation and preflight are
performed by deliver2.py.
