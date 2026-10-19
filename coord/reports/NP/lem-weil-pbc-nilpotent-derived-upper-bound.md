## Worker report

The module `Sheaf.Algebra.Homology.NilpotentDerivedUpperBound` states
`DerivedCategory.isZero_homology_of_nilpotent_derived_reduction`, with `sorry` as its
entire proof. No definition or theorem is proved and no new definition node is needed.
The natural-language statement, source and proof of the item are unchanged.

Hypothesis and clause correspondence:

- A commutative ring is `{A : Type u} [CommRing A]`, with arbitrary universe `u`.
- Its ideal is `(I : Ideal A)`.
- The witness to nilpotence is `(N : ℕ) (hN : 1 ≤ N) (hI : I ^ N = ⊥)`.
  Quantifying over the witness expresses precisely the assumption that such an N exists.
- Ordinary A-modules are encoded by the existing `CategoryTheory.RingSiteModules A`:
  sheaves of modules over `CochainComplex.onePointRingSheaf A` on
  `Discrete PUnit` with bottom topology. This site has one object and only its identity
  arrow; the bottom topology requires just the identity covering. The quotient uses
  the same encoding, with coefficient ring `A ⧸ I`.
- The chosen localizations are the two `HasDerivedCategory.{w}` instances. This is the
  size convention of the recorded abstract-derived-category dependency, rather than
  a boundedness, finiteness or projectivity assumption on C.
- `(C : DerivedCategory (RingSiteModules A))` is the arbitrary unbounded object of D(A).
- The quotient map is `Ideal.Quotient.mk I`; `ringSiteMap` is its map of ring sheaves.
- `E`, `hobjects`, `hmaps`, and `[E.Additive]` specify termwise extension of scalars
  by the exact object and morphism formulas in `SheafOfModules.derivedChangeOfRings`.
  They are presentation data for the stated tensor functor, not a different ring map.
- `LF`, `ε`, and `hLF` specify its left derived functor relative to the quasi-isomorphisms
  in the homotopy category, again using the recorded dependency's universal property.
  Thus `LF.obj C` is the node's C-bar. The theorem holds for any choices satisfying
  these formulas and universal property. Their existence is already furnished by
  `SheafOfModules.derivedChangeOfRings`, and uniqueness of a left derived functor makes
  the vanishing assertion independent of the choice. No additional Tor bound is assumed.
- The degree bound is `(b : ℤ)`, with no restriction on its sign.
- `hred : ∀ i : ℤ, b < i → IsZero ((homologyFunctor ... i).obj (LF.obj C))`
  is exactly H^i(C-bar)=0 for every i>b.
- The conclusion is `∀ i : ℤ, b < i → IsZero ((homologyFunctor ... i).obj C)`:
  the same upper bound for C, without any lower bound or claim at degree b.
  `IsZero` is used on module-category objects, not on bare carrier types.

Statement dependencies read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory` (docstrings and signatures at lines 71–87), as recorded by
  `def-weil-abstract-derived-category`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`:
  `SheafOfModules.derivedChangeOfRings` (full module and signature read).
  Its existential additive extension, map formula, counit and `IsLeftDerivedFunctor`
  property give the precise interface used above.
- Added the already landed node `def-pc-ring-hom-extension-shared-definitions` to
  `stmt_deps`, as permitted by brief-stage2 §5 for existing landed notions.
  `Sheaf.Algebra.Homology.RingHomExtensionDefs`: `CategoryTheory.RingSiteModules`
  and `CategoryTheory.ringSiteMap` (full module read). These reuse
  `CochainComplex.onePointRingSheaf` from
  `Sheaf.Algebra.Homology.KFlatTensorQuasiIso`, also read. No dependency node is edited.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` (lines 29–41) gives precisely the cohomology
  induced through localization of cochain complexes.

The stated proof dependencies are imported without `public`: Flat, BoundedFlatReplacement,
KFlatClosure, KFlatResolution, BoundedFlatKFlat, AcyclicKFlatTensor, and the upstream
HomotopyCategory.Acyclic. Their node records and statements were read. The unstated
`lem-pur-kflat-change-of-rings` has no recorded module and so supplies no import yet;
it remains explicitly named in the six-step proof docstring. The abstract derived category
and derived change of rings are available through public statement imports.

Source read: `literature/stacks-project/more-algebra.tex`, lines 17306–17351,
Tag 0H75, `lemma-check-tor-dimension-modulo-nilpotent`. Its filtration proof first treats
modules killed by I, then inducts using IM and M/IM. This item's recorded proof is the
upper-bound-only adaptation: it supplies a bounded-above flat replacement of the reduction
before using that filtration, and assumes no finite lower Tor bound. The complete six-step
node argument, including its cycle-lifting exactness argument, appears in the theorem's
docstring. No source correction or statement dispute was found.

Edge cases checked before writing: I=0 (including N=1) gives identity reduction; the zero
ring is allowed, and I=top with nilpotence forces precisely that case. C=0 is allowed.
Positive, zero and negative b all use the same strict inequality, and unbounded complexes
remain allowed. No characteristic, Noetherian, local, finite-generation or nontriviality
assumption appears. Arbitrarily large module universes can be included by enlarging u;
the two localizations use a common arbitrary morphism-size universe w, as in the dependency.

Searches run:

- `msearch.py`, LeanFinder: “Derived reduction modulo a nilpotent ideal detects vanishing
  of cohomology above an integer”. Eight hits concerned cotangent complexes, ordinary Tor
  of projective objects, and injective complexes; no nilpotent derived-bound detection.
- `msearch.py`, Loogle: `"nilpotent", "tensor"`. Two hits:
  `LieModule.instIsNilpotentTensor` and `isNilpotent_tensor_residueField_iff`;
  neither is a theorem about cohomology of derived reduction.
- `msearch.py`, grep: `nilpotent.*(derived|tensor|isLE)|(derived|tensor|isLE).*nilpotent`.
  Fifteen Mathlib hits concerned prime spectra, exponential nilpotence and Lie algebras;
  none states the item.
- `msearch.py`, LeanSearch: “Derived reduction modulo a nilpotent ideal detects upper
  cohomological bounds”. UNAVAILABLE: service returned Internal Server Error.
- `rg` of the upstream `WeilConjectures` tree for the item id and
  `nilpotent.*(derived|tensor)|(derived|tensor).*nilpotent`: only an unrelated
  RingTheory.TensorProduct.Maps comment, no matching declaration.
- `rg` of `lean/Sheaf` for nilpotent derived/tensor/upper-bound combinations and the
  proposed declaration name: unrelated algebraic geometry and field-theory lemmas only.
  Searches for one-object sites and ring scalar extension found the shared definitions
  used here, eliminating the need for a new notion.

Validation: the delivered module compiled cleanly with `scompile.py` on the project
server (1.8 seconds, nice 19, two threads, 60-second file limit). No local compiler was run.


## Second reading by NP

I independently read the node, its six proof steps, the complete delivered Lean module,
its three statement-dependency nodes and their recorded declarations, and the relevant
Mathlib definitions. No statement correction, new definition node, or dependency module
is present or needed. The only added statement dependency is the already landed
`def-pc-ring-hom-extension-shared-definitions`; its `RingSiteModules` and `ringSiteMap`
are the existing notions needed by this statement.

The node's objects, hypotheses, and conclusion, matched individually:

1. An arbitrary commutative ring A: `{A : Type u} [CommRing A]`. Exact; no field,
   characteristic, locality, Noetherian, finite-generation, or nontriviality assumption.
2. An ideal I in A: `(I : Ideal A)`. Exact; not required to be proper or finitely generated.
3. A positive nilpotence exponent: `(N : ℕ) (hN : 1 ≤ N) (hI : I ^ N = ⊥)`.
   Exact: the theorem can be applied to any witness of the node's existential assumption;
   conversely these parameters supply such a witness. No fixed exponent is imposed.
4. The ordinary module category and D(A): `RingSiteModules A` and
   `DerivedCategory (RingSiteModules A)`, with its `HasDerivedCategory.{w}` binder.
   Exact under the node's expressly specified one-object-site encoding. I opened
   `RingHomExtensionDefs.lean` and `KFlatTensorQuasiIso.lean`: the category is
   `Discrete PUnit.{u+1}`, the topology is bottom, and `onePointRingSheaf` is the actual
   constant presheaf with value A, with `Presheaf.isSheaf_bot` as its sheaf proof.
   A module sheaf here is an ordinary A-module. This is not an étale or pro-étale site.
   Mathlib `HasDerivedCategory` chooses a localization with morphisms in universe w;
   `DerivedCategory` localizes all integer cochain complexes, not a bounded subcategory.
5. An arbitrary C in D(A): `(C : DerivedCategory (RingSiteModules A))`. Exact.
6. The quotient and its derived category: `A ⧸ I` and the second
   `HasDerivedCategory.{w} (RingSiteModules (A ⧸ I))` binder. Exact. The map is the
   canonical `Ideal.Quotient.mk I`, passed to the shared `ringSiteMap` construction.
7. The reduced object C-bar: `LF.obj C`. I checked all presentation parameters:
   `E`, `hobjects`, `hmaps`, `[E.Additive]` specify the objectwise and morphismwise
   extension of scalars in `SheafOfModules.derivedChangeOfRings`, with the equality
   transports in the correct directions. `ε` has source `Qh ⋙ LF` and target the
   termwise E functor followed by target localization. `hLF` is precisely
   `LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso ... (ComplexShape.up ℤ))`.
   Mathlib `Functor.IsLeftDerivedFunctor` is the right-Kan-extension universal property,
   and `Functor.leftDerivedUnique` identifies any two such choices. The recorded
   `derivedChangeOfRings` theorem supplies this data, together with the K-flat computation.
   Thus these parameters present the node's derived tensor; they do not assume an extra
   property of C or replace derived tensor by ordinary tensor. Omitting the dependency's
   triangulatedness and K-flat-counit clauses as hypotheses does not change the object:
   uniqueness identifies this LF with the supplied derived extension. IsZero cohomology
   is invariant under that isomorphism.
8. An arbitrary integer b: `(b : ℤ)`. Exact; not a natural number or nonnegative bound.
9. The sole vanishing hypothesis: `hred : ∀ i : ℤ, b < i →
   IsZero ((homologyFunctor (RingSiteModules (A ⧸ I)) i).obj (LF.obj C))`.
   Exact. I read `DerivedCategory.homologyFunctor` and `homologyFunctorFactors` in
   Mathlib: this is the cohomology induced from integer cochain complexes by localization.
10. The conclusion: `∀ i : ℤ, b < i →
    IsZero ((homologyFunctor (RingSiteModules A) i).obj C)`. Exact: same b, all degrees
    strictly greater than b, no assertion at b, no lower bound, and no finite Tor interval.
    `IsZero` concerns objects of the abelian module-sheaf category, not bare types.

Source check: I read `more-algebra.tex`, Tag 0H75, lines 17306–17351, and Tag 09AR,
`lemma-lift-complex-projectives`, lines 19468–19495. The former assumes an arbitrary
surjective ring map with nilpotent kernel, not a Noetherian ring or bounded complex.
The quotient map realizes that setting. Its printed conclusion concerns two-sided Tor
amplitude; this node expressly states the upper-bound-only adaptation, not a literal
restatement of that conclusion. The node's six-step argument supplies the intermediate
upper tensor bound by good truncation and bounded-above flat replacement, then applies
the same nilpotent filtration. This justifies exactly the cohomological upper-bound
assertion used to obtain D-minus in 09AR, without importing a nonexistent lower bound.

I also opened the signatures of the imported proof dependencies: flatness is exactness
of tensor, bounded flat replacement preserves the specified upper bound, K-flat resolution
has flat terms, KFlatClosure provides its mapping-cone clause, AcyclicKFlatTensor permits
an arbitrary other complex, and the upstream cone criterion is quasi-isomorphism iff
acyclic cone. BoundedFlatKFlat uses ordinary `ModuleCat`; transporting across the
one-point module-category equivalence belongs to stage 3, not a new notion in this
statement. The unstated K-flat change-of-rings node has no module to import, as the worker
correctly reports. No dependency module is delivered here.

Edge cases: I=0 gives identity derived reduction and permits N=1. N=0 is correctly excluded
as a nilpotence witness by the node itself; any nilpotent ideal, including in the zero ring,
has a positive witness. I=top plus nilpotence forces the zero ring, which is allowed.
C=0 is allowed. Every integer b, in particular b=0 and negative b, is included. There is
no index family or scheme in the statement, so empty index sets and empty schemes add
no cases. No characteristic is restricted. The ring and module sizes use arbitrary u,
with arbitrary localization morphism universe w as in the dependency; larger modules
can be included by increasing u. All binders and universes are explicit and bound.

Independent reuse searches (different wording from the worker):

- `msearch.py ... leanfinder "Nilpotent quotient derived Nakayama reflects coconnective
  complexes"`: eight hits on injective/projective complexes, K-injectivity, CM5b, and
  `DerivedCategory.isGE_Q_obj_iff`; none concerns reduction along a nilpotent quotient.
- `msearch.py ... loogle '"nilpotent", "homology"'`: zero hits.
- `msearch.py ... grep 'nilpotent.*(cohomology|homology|coconnective)|
  (cohomology|homology|coconnective).*nilpotent'`: zero hits.
- Direct `rg` of pinned Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for nilpotence with homology, cohomology, coconnectivity, derived, or boundedness:
  only unrelated Lie derived-series, group nilpotence, Noetherian sections, and a
  comment in UniversalH0ProjectiveNormalization. No existing matching statement.
  Direct declaration-name and nilpotent-upper-bound searches likewise found no duplicate.

H5–H9: this delivery has no definitions, no private copy or hollow data, and one theorem
whose entire proof is `sorry`. Both docstrings cite the source and blueprint id. The
statement docstring carries all six node proof steps, including the tensor-cone symmetry,
quotient balancing formulas, and the cocycle-lifting argument. The imports use the
recorded dependencies. The namespace and module path follow the project conventions;
all Lean lines are at most 100 characters. I checked programmatically that `lean.statement`
is verbatim the source signature, and checked the variables by eye.

Mismatches and changes: none. I preserved the correct Lean and node records and appended
this independent reading. The server-only `scompile.py` compilation of the sole module
passed cleanly in 1.7 seconds, nice 19, two threads, 60-second per-file limit; no local
compiler or global build was run.
