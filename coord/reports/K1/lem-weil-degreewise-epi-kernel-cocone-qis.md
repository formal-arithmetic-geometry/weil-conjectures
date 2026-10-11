## Worker report

The module `Sheaf.Algebra.Homology.KernelShiftedMappingCone` states
`CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi`, with its sole
proof `sorry`. No definitions or dependency modules are added and no node correction is needed.

Hypothesis and clause correspondence:

- An arbitrary abelian category A is `{C : Type u} [Category.{v} C] [Abelian C]`.
  All universes `u`, `v`, `w` are explicit. `[HasDerivedCategory.{w} C]` chooses the
  localization in the morphism universe of the dependency's size convention; it is not
  an extra mathematical restriction (Mathlib provides `HasDerivedCategory.standard`).
- P and Q are `{P Q : CochainComplex C ℤ}` and the complex morphism is `(f : P ⟶ Q)`.
- Each degree map is epic: `(hf : ∀ p : ℤ, Epi (f.f p))`. This does not require a
  degreewise splitting, injectives, boundedness, products, or an enough-injectives hypothesis.
- K and its inclusion are Mathlib's `kernel f` and `kernel.ι f` in the category of
  complexes. `HomologicalComplexLimits` constructs limits termwise and its evaluation
  functors preserve finite limits, so this is precisely the termwise kernel with the
  restricted differential, up to the canonical kernel isomorphisms.
- The cone and shift are `(mappingCone f)⟦(-1 : ℤ)⟧`. Mathlib's cone orders its
  summands as P^(r+1) ⊞ Q^r, while the node writes Q^r ⊕ P^(r+1). The canonical
  interchange of summands identifies these conventions. The identities `d_fstX` and
  `d_sndX` in `HomotopyCofiber` give (-d_P x, d_Q y + f x). Multiplication of the
  differential by -1 under the shift gives (d_P x, -d_Q y - f x), exactly the
  displayed differential after exchanging the two components.
- The assertion that κ^p=(0,ι^p) forms a complex morphism is the existential binder
  `∃ κ : kernel f ⟶ (mappingCone f)⟦(-1 : ℤ)⟧` together with the two component
  equations for every p. The `shiftFunctorObjXIso` transports degree p to cone degree
  p-1; the `sndX` (Q) projection is zero and the `fstX` (P) projection is
  `(kernel.ι f).f p`. These jointly specify precisely the displayed maps, since
  the two biproduct projections are jointly monic (`homotopyCofiber.ext_to_X`).
  Thus existentially stating the map does not weaken the assertion about the prescribed κ.
- κ is a quasi-isomorphism: `QuasiIso κ`, the Mathlib predicate that every cohomology
  map is an isomorphism.
- The final derived-category isomorphism is
  `Nonempty (DerivedCategory.Q.obj (kernel f) ≅
  DerivedCategory.Q.obj ((mappingCone f)⟦(-1 : ℤ)⟧))`. The same localization Q of
  the dependency is used on both objects.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (imported through DerivedCategory.Basic).
  Read its full class declaration and explanatory docstring: preadditive, normal
  monos/epis, finite products, kernels and cokernels.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, in `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the
  recorded localization and chosen morphism-universe signatures were read.
  Its constituent notions are the existing `CochainComplex`, `QuasiIso`,
  `CochainComplex.mappingCone`, and the shift. Read the full signature and docstring
  of `QuasiIso` in `Algebra.Homology.QuasiIso`, `mappingCone` and its projections
  in `HomotopyCategory.MappingCone`, `shiftFunctorObjXIso` and `shiftFunctor_obj_d'`
  in `HomotopyCategory.Shift`, and `fstX`/`sndX` and their differentials in
  `HomotopyCofiber`.

Source read: local `literature/stacks-project/derived.tex` is absent on this machine.
Read the source online at https://stacks.math.columbia.edu/tag/070M and
https://stacks.math.columbia.edu/tag/014Q. Tag 070M uses the short exact sequence
of complexes to give a distinguished triangle; the node supplies the chain-level
comparison proof, reproduced step by step in the theorem docstring. The three proof
steps are kernel/chain-map construction; exact sequence with contractible identity
cone quotient; and triangle comparison plus cohomology factorization.

Edge cases checked before writing: f=identity gives the zero kernel and contractible
shifted cone; Q=0 gives kernel=P and the canonical shifted-cone copy of P; P=0 forces
Q=0 under the epic hypothesis. Zero categories are allowed. All integer degrees,
including negative degrees and degree 0, are quantified. Complexes need not be bounded.
No characteristic or set-size restriction is introduced. The shift at -1 and the
component signs were checked against Mathlib's differential formulas. No statement
fault or STATEMENT-DISPUTED concern was found.

Searches performed (all with group K1 and this item):

- msearch.py leanfinder: "kernel of a degreewise epimorphism of cochain complexes is
  quasi-isomorphic to the shifted mapping cone". Eight hits; nearest is
  `CochainComplex.mappingCone.quasiIso_descShortComplex`, mapping the cone of the
  first arrow in a short exact sequence to its third object, not this kernel map.
- msearch.py loogle: `CochainComplex.mappingCone, QuasiIso`. Two hits:
  `quasiIso_descShortComplex` and the injective factorization `cm5b` projection;
  neither states this assertion.
- msearch.py grep: `quasiIso.*(kernel|Cone)|kernel.*(mappingCone|quasiIso)` in
  `Algebra/Homology`. Five hits on CM5a/CM5b constructions, no exact match.
- msearch.py leansearch: "kernel of a degreewise epimorphism is quasi-isomorphic to
  the shifted mapping cone". Service unavailable: Internal Server Error.
- rg of `kernel.*cone|kernel.*Cone|cocone|degreewise.*epi` in the source project's
  `WeilConjectures` and the present project's `lean/Sheaf`: unrelated cocones and
  cardinal-generated/functorial-homotopy results, no matching declaration.
- grep of this item's literal id in `WeilConjectures`: no hits.
- rg of the proposed declaration stem `kernel_to_shifted_mappingCone|degreewise_epi_kernel`
  in `dag/lean_names_upstream.json`, `WeilConjectures`, and `lean/Sheaf`: no hits.

Validation: scompile.py compiled the single module on the server in 1.5 seconds,
exit code 0, without errors or warnings. The delivery dry run is the final gate;
the independent second reader is to write its own section and perform the delivery.

## Second reading by K1

Independent review of the repository node, the sandbox node and module, both statement
 dependency nodes, their recorded Mathlib declarations, and the Stacks source. Verdict:
 the Lean says exactly what the node says. No mathematical or typing mismatch was found;
 the module and node record are unchanged. This section is the only delivery change by
 the second reader. There are no new definition nodes, dependency modules, or statement
 corrections to review.

Object/hypothesis/conclusion checklist (the node's statement in order):

1. Arbitrary abelian category A: `{C : Type u} [Category.{v} C] [Abelian C]`.
   PASS. Read `CategoryTheory.Abelian` in `CategoryTheory/Abelian/Basic.lean`, the
   declaration of def-sp-abelian: preadditivity, normal monos/epis, finite products,
   kernels and cokernels, with zero objects and finite biproducts derived. No additional
   exactness, injectivity, product, or ring hypothesis is introduced.
2. Integer-indexed cochain complexes P,Q and a morphism f: `{P Q : CochainComplex C ℤ}`
   and `(f : P ⟶ Q)`. PASS. `CochainComplex` abbreviates `HomologicalComplex` with
   `ComplexShape.up ℤ`; its differentials square to zero and its morphisms commute
   with differentials. Neither complex is required to be bounded.
3. Every f^p epic: `(hf : ∀ p : ℤ, Epi (f.f p))`. PASS. All degrees are quantified,
   with no splitting or enough-injectives assumption.
4. K is the termwise kernel with its restricted differential, and ι its inclusion:
   `kernel f` and `kernel.ι f`. PASS. Read the termwise limit construction
   `HomologicalComplex.coneOfHasLimitEval`, its universal-property proof, and the
   degree-evaluation limit-preservation instances in `HomologicalComplexLimits.lean`.
   Thus each evaluated kernel is canonically the kernel of f^p; its differential
   is the induced restriction. The node does not prescribe a different chosen kernel.
5. Cone(f)^r = Q^r ⊕ P^(r+1), d(y,x) = (d_Q y + f x,-d_P x): `mappingCone f`.
   PASS after the canonical interchange of summands. Read `mappingCone` and
   `homotopyCofiber.fstX`, `sndX`, `d_fstX`, and `d_sndX`. The P projection is
   `fstX`, the Q projection is `sndX`, and their differential equations are precisely
   the node's equations in the exchanged order. These are existing dependency notions,
   not a private cone construction.
6. Cone(f)[-1]^p = Q^(p-1) ⊕ P^p with d(y,x) = (-d_Q y-f x,d_P x):
   `(mappingCone f)⟦(-1 : ℤ)⟧`. PASS. Read `shiftFunctorObjXIso` and
   `shiftFunctor_obj_d'`: the degree is p+(-1) and the differential is multiplied
   by (-1)^(-1)=-1. The stated transport to degree `p - 1` includes no extra sign.
7. The prescribed κ^p=(0,ι^p) forms a complex morphism:
   `∃ κ : kernel f ⟶ (mappingCone f)⟦(-1 : ℤ)⟧` and its two projection equations
   under `∀ p : ℤ`. PASS. The first is zero on the Q^(p-1) projection; the second
   is `(kernel.ι f).f p` on the P^p projection. Read `homotopyCofiber.ext_to_X`:
   these two projections are jointly monic, so this existential specifies the exact
   prescribed map, not an arbitrary quasi-isomorphism. A complex morphism supplies
   differential compatibility. The arithmetic witnesses use only equalities of integers.
8. This same κ is a quasi-isomorphism: `QuasiIso κ`. PASS. Read `QuasiIso`,
   `QuasiIsoAt` and `quasiIsoAt_iff_isIso_homologyMap` in `QuasiIso.lean`:
   this is invertibility on every cohomology object, in the dependency's sense.
9. In particular K ≅ Cone(f)[-1] in D(A):
   `Nonempty (DerivedCategory.Q.obj (kernel f) ≅
   DerivedCategory.Q.obj ((mappingCone f)⟦(-1 : ℤ)⟧))`. PASS. Read
   `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory` and
   `DerivedCategory.Q` in `DerivedCategory/Basic.lean`, as recorded by
   def-weil-abstract-derived-category. `[HasDerivedCategory.{w} C]` expresses the
   chosen localization and morphism-size convention already in that dependency.
   At w=max u v, `HasDerivedCategory.standard C` is available for every abelian C;
   the statement also permits any smaller localization universe when available.
   Thus arbitrary u,v,w introduce no extra mathematical restriction. Both objects
   use the same localization. The node asks for an object isomorphism, so `Nonempty`
   has exactly the required logical strength.

Source check: the local Stacks .tex is absent. Read the upstream raw Stacks
`derived.tex`, saved only in sandbox `scratchpad/derived.tex`: the standing additive
category context and `definition-cone` at lines 2458-2492, and
`lemma-difficulty-K-injectives` (070M) with its proof at lines 10588-10658.
Also read https://stacks.math.columbia.edu/tag/070M and
https://stacks.math.columbia.edu/tag/014Q. The explicit cone matrix agrees with the
node and Lean. Tag 014Q defines distinguished triangles; the cone formula itself
is at `definition-cone`. Tag 070M uses countable products and enough injectives to
construct its particular inverse system and split sequence. This node deliberately
extracts the general kernel comparison from that argument; those assumptions are
not needed for the comparison once f is given and degreewise epic. In an arbitrary
abelian category the node's quotient is Cone(id_Q)[-1], which is contractible;
its short exact sequence gives the derived-category triangle. No hypotheses were
silently omitted from the extracted assertion.

Edge cases: f=id_P gives a zero kernel and a contractible cone; Q=0 gives the
kernel P and shifted cone canonically P; P=0 with the epic hypothesis forces Q=0.
The zero abelian category is permitted. All negative degrees and p=0 are covered;
unbounded complexes are permitted. There is no variable index set, scheme, or
characteristic parameter, so empty indexing/empty scheme questions impose no extra
condition here. In characteristic two the signs become equal in the category as
expected, without a characteristic exclusion. Universes are explicitly bound and
independent, with standard localization available at max u v.

Independent searches, using different wording from the worker:

- msearch leanfinder: "canonical inclusion of the kernel into the mapping cocone
  is a quasi-isomorphism when the chain map is surjective in every degree".
  Eight hits, including `CochainComplex.mappingCone.quasiIso_descShortComplex`.
  Opened its declaration and surrounding construction: it maps the cone of the
  first morphism of a short exact sequence to the third complex; it does not state
  the specified kernel inclusion into the shifted cone of the second morphism.
- msearch loogle: `CochainComplex.mappingCocone, QuasiIso`: zero hits.
  An initial query with `HomologicalComplex.QuasiIso` was rejected as an unknown
  identifier; repeated with the actual unqualified predicate, successfully.
- msearch grep: `mappingCocone|quasiIso_descShortComplex`: nineteen hits.
  Opened `HomotopyCategory/MappingCocone.lean`: its existing mapping cocone is
  definitionally the shifted cone already used here; no kernel comparison theorem
  is declared there. CM5a and CM5b are factorization constructions, not this statement.
- msearch leansearch: "For a surjective morphism of cochain complexes, its kernel
  includes quasi-isomorphically into its homotopy fiber". Service unavailable
  (Internal Server Error); no mathematical verdict inferred from that failure.
- Independent rg of Mathlib's `Algebra/Homology`, source `WeilConjectures`, and
  repository `lean/Sheaf` for kernel/epi/surject/shortExact with mappingCone or
  mappingCocone, and for `homotopy.?fiber|mapping.?cocone|shifted.?cone|kernel.*cone|cone.*kernel`.
  Only generic cocone constructions, factorization applications, and unrelated
  quotient/telescope statements in the project; no declaration of this assertion.
- Exact proposed name stems `kernel_to_shifted_mappingCone|degreewise_epi_kernel`
  and the blueprint id in source `WeilConjectures`, repository `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no hits. No declaration collision or duplicate
  notion was found. Existing Mathlib cones, shifts, kernels, and localization are used.

H5/H6/H8/H9: no definition or hollow data, one theorem with a sole `sorry` proof;
no mathematical proof was added. The module and declaration docstrings name the
source and exact blueprint id. The theorem docstring follows all three node steps:
construct the kernel map; form the short exact sequence with contractible identity
cone quotient; compare its triangle with the identity triangle and use cohomology
factorization. Both imports serve used constructions. No line exceeds 100 characters;
all category and universe variables are explicitly bound. Parsed the sandbox node:
`lean.statement` equals the file's theorem signature verbatim, and only `lean`
differs from the repository node. No statement_change or citer verdicts are required.

Validation: second-reader scompile of the original module passed on the server
in 1.4 seconds, exit code 0, with no errors or warnings. Delivery preflight and
compile are checked again by deliver2.py before pushing.
