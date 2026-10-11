## Worker report

The module states the natural surjection from preceding tensor cohomology to the first Tor
of the opcycle cokernel. It leaves the proof as `sorry`.

The commutative ring is `(A : Type u) [CommRing A]`. The one-point-site specialization is
the category `ModuleCat.{u} A`; its cochain complex is
`(P : CochainComplex (ModuleCat.{u} A) ℤ)`. The integer is `(a : ℤ)`. Flatness of every term
is `(hflat : ∀ i : ℤ, Module.Flat A (P.X i))`, with no boundedness requirement.

The quotient `Q = P^a / im(d^(a-1))` is `P.opcycles a`. For each module `N`, its
degree-zero complex is `(CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N`.
`MonoidalCategory.curriedTensor` and `map₂CochainComplex` form the total tensor complex;
`HomologicalComplex.homologyFunctor ... (a - 1)` selects its preceding cohomology.
`(Tor' (ModuleCat.{u} A) 1).obj (P.opcycles a)` is the Tor functor in `N`.
The natural transformation `τ` expresses naturality for every map of modules, and
`∀ N, Epi (τ.app N)` expresses surjectivity of every component in `ModuleCat`.

Statement dependencies used: `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex`;
`Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor` (through
`map₂CochainComplex`); `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
`HomologicalComplex.homologyFunctor`; `Mathlib.RingTheory.Flat.Basic`, `Module.Flat`;
`Mathlib.CategoryTheory.Monoidal.Tor`, `CategoryTheory.Tor'`. The related `Acyclic`
declaration is not needed to take cohomology. Each dependency's Mathlib declaration
was checked against its node; no dependency module is needed.

Edge cases: `a` is any integer, including zero and negative indices; `N` may be zero;
`P` may be the zero complex. The module category and unbounded `ℤ` complex retain these
cases. Flatness is required termwise even for zero terms. The categorical epi condition
is surjectivity for module maps.

Searches: `msearch.py leanfinder` with “natural surjection from preceding homology of
tensor of flat cochain complex to Tor one of degree cokernel” returned Tor computation
and flatness results, but no matching surjection. `msearch.py loogle` with
`CategoryTheory.Tor, CochainComplex.mapBifunctor, HomologicalComplex.opcycles` returned
zero hits. `msearch.py grep` for `opcycles.*Tor|Tor.*opcycles` in `Algebra/Homology`
returned only separate opcycle APIs. `rg` in Mathlib homology files found no matching
surjection; `rg` and `grep -rn` in the source library, and `rg` in `lean/Sheaf`,
found no matching declaration. The Stacks source file is absent from this machine's
`literature/` copy; the node's source and proof steps supplied its wording here.

## Earlier second reading (a previous round; superseded)

Pending independent reading by the second worker. The first worker's clause-by-clause
comparison is in the worker report above; the second worker should replace this note
after checking the node and the Lean file independently.

## Second reading by G1

I independently opened the item's node, its module, all five statement-dependency nodes,
and the Mathlib declarations below. The Lean statement says exactly what this module
lemma says; no signature or node-statement correction was necessary.

Object/hypothesis/conclusion inventory and comparison:

1. A commutative ring A, regarded as the structure ring on the one-point site:
   `(A : Type u) [CommRing A]`, with category `ModuleCat.{u} A`. PASS. The node explicitly
   specializes to ordinary modules, so the generic site dependencies specialize to this
   category; no scheme, topology or nonempty-site hypothesis is being added.
2. An integer-indexed cochain complex P: `(P : CochainComplex (ModuleCat.{u} A) ℤ)`.
   PASS. I read `CochainComplex` in Mathlib.Algebra.Homology.HomologicalComplex: its shape
   is `.up ℤ`, and differentials square to zero. This is the dependency's generic
   definition applied to the one-point module category, not a bounded complex.
3. Every term flat: `(hflat : ∀ i : ℤ, Module.Flat A (P.X i))`. PASS. The misleadingly
   named dependency def-weil-pbc-flat-ring-map includes flat *modules*, not only ring
   maps. I read `Module.Flat.iff_lTensor_preserves_injective_linearMap` in
   Mathlib.RingTheory.Flat.Basic, verifying equivalence with the node's definition.
   No projectivity, finite generation, Noetherianity or field hypothesis is added.
4. An arbitrary integer a: `(a : ℤ)`. PASS; no positivity assumption.
5. Q = P^a/im(d^(a-1)): `P.opcycles a`. PASS. I read
   `HomologicalComplex.opcycles := (K.sc i).opcycles` and
   `ShortComplex.moduleCatOpcyclesIso` in Mathlib.Algebra.Homology.ShortComplex.ModuleCat,
   identifying this with the quotient of the middle module by the range of the incoming
   differential. For `.up ℤ` that incoming degree is a-1.
6. Every A-module N and P tensor N, with N in degree zero:
   `CochainComplex.singleFunctor (ModuleCat.{u} A) 0`, followed by
   `((MonoidalCategory.curriedTensor ...).map₂CochainComplex).obj P`. PASS. I read
   `singleFunctors` in HomotopyCategory.SingleFunctors and `map₂CochainComplex` in
   Bifunctor, whose object is `HomologicalComplex.mapBifunctor`; the BifunctorShift
   specialization is precisely the total complex in def-pc-tensor-complex-sheaves.
   In degree n the only nonzero summand is P^n tensor N; the second differential is
   zero. Thus the total-complex presentation gives the node's termwise tensor complex.
7. Source H^(a-1): the final `HomologicalComplex.homologyFunctor ... (.up ℤ) (a - 1)`.
   PASS. I read its object/map definition in ShortComplex.HomologicalComplex, and the
   dependency def-pc-acyclic-complex-modules, which includes cohomology as well as
   acyclicity. No acyclicity assumption is present or needed.
8. Target Tor_1^A(Q,N): `(Tor' (ModuleCat.{u} A) 1).obj (P.opcycles a)`. PASS. I read
   Mathlib.CategoryTheory.Monoidal.Tor: Tor' derives the FIRST tensor argument and then
   flips the functor, so this fixes Q and leaves N variable, just as the dependency's
   projective-resolution definition requires. ModuleCat.Abelian, Monoidal.Basic and
   Projective supply the categorical instances for every commutative ring; these are
   not additional mathematical assumptions on A or P.
9. An A-linear surjection natural in N: `∃ τ : ... ⟶ ..., ∀ N, Epi (τ.app N)`.
   PASS. Functor-category morphisms are natural transformations, so one transformation
   is chosen before quantifying its components, expressing compatibility with every
   module map N -> N'. Its components are ModuleCat morphisms, hence A-linear.
   I checked `ModuleCat.epi_iff_surjective` in ModuleCat.EpiMono. The conclusion asks
   for existence and surjectivity, not an isomorphism or a chosen canonical map.

Source reading: the local literature copy contains no Stacks source, so I fetched the
upstream `more-algebra.tex` into the sandbox's scratchpad and read
`lemma-last-one-flat` (Tag 0653), including the surrounding Tor-dimension section and
chapter introduction. The stable tag is now numbered 15.68.2 on the website; the node's
15.59.2 is an older numbering. Source: https://stacks.math.columbia.edu/tag/0653 and
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex.
The source's larger flat-cokernel lemma assumes boundedness and Tor amplitude in order
to obtain vanishing of the preceding tensor cohomology. The delivered node isolates
only its module Tor obstruction argument. Its four proof steps construct the surjection
without those larger hypotheses: flatness of P^a kills Tor_1(P^a,N), tensor right
exactness supplies lifts, and the complex relation kills boundaries. Consequently no
boundedness, amplitude or exactness hypothesis is missing from this auxiliary lemma.

Edge cases: P and N may be zero, the ring may be the zero ring, and a may be zero or
negative. The statement excludes none of them. For N=0 both sides vanish. There is no
finite index set, dimension bound, characteristic condition or scheme; the empty scheme
is not an object of this one-point module statement. `u` is declared and arbitrary;
Mathlib's ModuleCat monoidal structure uses a common universe for the ring and modules
(as documented in Monoidal.Basic). This is the usual common-universe presentation,
with no fixed universe level or restriction to finite/countable modules; objects at
other sizes are represented in a common larger universe using universe lifts. All
variables and the sole universe are explicitly bound.

Independent searches, using different words from the first worker:

- LeanFinder: `first derived tensor of differential cokernel quotient of cycles modulo
  boundaries` returned tensor differential formulas, Rep.torIso and unrelated boundary
  maps. None states the natural surjection for an arbitrary flat module complex.
- Loogle: `"opcycles", "Tor"` returned opcycles functor APIs, with no matching surjection.
- LeanSearch: `surjective natural transformation from tensor cohomology to Tor of
  cokernel` returned UNAVAILABLE (HTTP Internal Server Error). This is a service failure,
  not a no-match verdict; the other searches and source inspection remain available.
- `msearch.py grep 'Tor.*opcycles|opcycles.*Tor'` returned separate opcycle APIs, not
  this lemma. Direct case-insensitive rg for Tor with opcycle/cokernel in Mathlib
  homology, the source WeilConjectures tree and this repository's lean/Sheaf found
  no matching surjection. I opened the related source `ObjectProperty.flat_opcycles_of_exactAt`
  in DerivedCategory.FlatModel: it proves flatness assuming tensor exactness and
  does not provide this natural transformation. `Rep.torIso` computes Tor from a
  projective resolution in a representation category, so it is not this node either.
- The full proposed declaration name has no match in the source tree, Mathlib files,
  lean/Sheaf or dag/lean_names_upstream.json. The existing dependency definitions are
  used directly; no duplicate notion, new definition node or dependency module is needed.

Mismatch found and repaired (H8): the theorem's original docstring lacked the source
place and compressed the argument without its flat-resolution vanishing calculation
and explicit surjectivity lift. I replaced only that docstring with the source tag and
label plus all four proof steps, naming the nodes they use. The module header already
met the source and blueprint convention. The signature, imports, namespace and node
record are unchanged. There are no new definitions, hollow definitions or proved
lemmas; the sole theorem remains `by sorry`. No statement_change is present or needed.

Validation: `scompile.py` compiled the revised module cleanly in 1.5 seconds, with
no warnings. A direct signature extraction confirmed `lean.statement` matches verbatim,
and all Lean lines have at most 100 characters. `deliver2.py --no-push` printed OK:
the packet compiles and passes the stage-2 preflight.
