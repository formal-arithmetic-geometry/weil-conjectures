## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum` states
`AlgebraicGeometry.RingedSpace.coherent_kernel_cokernel_sum`, with one `sorry`
and no new definitions or proofs. No node fields other than `lean` change.

Hypotheses and clauses:
- `X : RingedSpace.{u}` renders the explicitly included general ringed-space case;
  schemes specialize by `X.toRingedSpace`. No Noetherian condition is imposed.
- `SheafOfModules.{u} (moduleRings X)` is the category of O_X-modules, and
  `f : F ⟶ G` is an O_X-linear map. `IsCoherent X F` and `IsCoherent X G`
  are exactly the two coherence hypotheses in (1). `kernel f` and `cokernel f`
  are Mathlib's categorical kernel and sheafified cokernel. Both conclusion
  predicates occur in the first conjunct.
- `S : ShortComplex ...` binds the three modules and two arrows (with zero
  composite); `S.ShortExact` means exactness, mono first arrow, epi second arrow,
  thus precisely the displayed sequence with zero ends in (2). The three
  implications list all choices of two coherent terms, giving the third.
- `r : ℕ` permits every r >= 0 and `F : Fin r → ...` lists its modules.
  `∀ i, IsCoherent X (F i)` binds all coherence hypotheses, and `IsCoherent X (⨁ F)`
  gives their finite direct sum in (3). A finite biproduct is the module direct sum.
- `IsCoherent X (0 : ...)` explicitly states the parenthesized r = 0 case.
- `∀ F G (_e : F ≅ G), IsCoherent X F → IsCoherent X G` is the final isomorphism
  clause. No extra coherence hypothesis is put on G.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (read the full structures; the theorem uses the permitted ringed-space generality).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, `SheafOfModules.Hom`;
  its linear natural-transformation category is the module category dependency's
  `mathlib_match`. No dependency replacement is needed.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`,
  the recorded `pqf-def-coherent` predicate, finite type and all finite free local
  relation kernels of finite type. Its imported `AlgebraicGeometry.moduleRings`
  from `Sheaf.Paper.DerivedHomMayerVietoris` is reused.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: `ShortComplex.ShortExact`
  (exact, mono, epi) is used directly, with no private exactness definition.

Edge cases: r = 0 is allowed, its Fin-indexed biproduct is a zero object and zero
coherence is also explicit; r = 1 gives a single summand up to iso. Zero maps
between coherent modules give source and target as kernel and cokernel; identity
maps give zero. Split exact sequences agree with the sum clause. Empty ringed
spaces/schemes are included without a nonempty binder. No commutativity,
Noetherian, affine, or field hypothesis is needed. The explicitly bound u is the
same module universe as the dependency predicate; every finite family can be
indexed by Fin r without an additional universe restriction.

Searches:
- msearch.py leanfinder: "coherent sheaves on a ringed space closed under kernels
  cokernels extensions finite direct sums": 8 hits on all-module abelian categories,
  quasicoherence, finite type and finite presentation, no closure theorem for coherence.
- msearch.py loogle: "SheafOfModules.IsFiniteType": 4 hits on finite-type definition,
  generators and finite-presentation implication, no closure theorem for coherence.
- msearch.py grep: "IsCoherent|isCoherent": 17 unrelated topological coherence hits.
- rg in source WeilConjectures and project lean/Sheaf for
  "IsCoherent|isCoherent|lem-weil-pbc-coherent-modules-kernel-cokernel-sum":
  existing RingedSpace.IsCoherent definition only; source Scheme.Modules.isCoherent
  denotes quasi-coherent finite presentation, explicitly distinguished from Stacks
  coherence outside the Noetherian case, so is not a replacement.
- The item's id has no upstream declaration hit. No existing declaration states
  all clauses of this node.

Source check: local literature/stacks-project/modules.tex is absent on this machine;
opened https://stacks.math.columbia.edu/tag/01BY directly. Its ringed-space hypotheses,
parts (3) and (4), and snake-lemma proof agree with the node. Finite sums follow
from (4) and the coherent zero module as explained in the node's proof. No
STATEMENT-DISPUTED issue or correction is needed. The docstring follows all seven
DAG proof steps, including the named dependencies, for stage 3.

Validation: scompile.py compiled the final module cleanly in 2.0 seconds (exit 0).
Mathlib HasFiniteBiproducts.of_hasFiniteProducts is enabled as a local instance
from Mathlib.CategoryTheory.Preadditive.Biproducts; this reuses its finite product
construction and introduces no declaration or extra hypothesis. ZeroObject is
opened for the existing categorical zero notation.
Delivery dry run: deliver2.py --no-push printed OK: compile and preflight passed
except the second reading, which the second reader writes; nothing pushed.
The final declaration name was also searched by rg in Mathlib, WeilConjectures,
lean/Sheaf and dag/lean_names_upstream.json: no collision. The prescribed grep -rn
for the node id in WeilConjectures likewise returned no hits.

## Second reading by E1

I read the item JSON and its seven proof steps, the delivered Lean module, all
three statement-dependency nodes and the declarations they record. I fetched
the Stacks `modules.tex` source into this item's scratchpad and read
`section-coherent`, `definition-coherent` (01BV), and
`lemma-coherent-abelian` (01BY), including its proof. I also read the earlier
`section-kernels` description of kernels, sheafified cokernels, and finite sums.
The source has an arbitrary ringed space and no Noetherian, nonempty, affine,
field, or characteristic assumption. Source:
https://raw.githubusercontent.com/stacks/stacks-project/master/modules.tex
(01BV around lines 1578ff; 01BY around lines 1641ff).

The node's objects, hypotheses, and conclusions matched individually:

1. Ambient scheme, explicitly allowing any ringed space: `X : RingedSpace.{u}`.
   Verdict: exact permitted generality; a scheme specializes via
   `X.toRingedSpace`. I read Mathlib `Scheme` (locally ringed space with local
   affine charts) and `Scheme.Hom`, recorded by `def-pc-scheme`, and Mathlib
   `RingedSpace` (a sheafed space of commutative rings).
2. Category of O_X-modules and its linear maps:
   `SheafOfModules.{u} (moduleRings X)` and `f : F ⟶ G`.
   Verdict: the `def-weil-sheaf-of-modules-category` Mathlib match is used.
   `SheafOfModules.val` is a presheaf of modules whose underlying abelian-group
   presheaf is a sheaf; `Hom.val` is a morphism of these presheaves of modules.
   `moduleRings X` merely forgets commutativity of the structure sheaf to
   `RingCat`; it introduces no replacement structure sheaf.
3. Two coherent modules in clause (1): `IsCoherent X F → IsCoherent X G`.
   Verdict: precisely the recorded `pqf-def-coherent` declaration from
   `Sheaf.AlgebraicGeometry.Coherent`. I opened its definition: finite type
   together with finite-type kernels of every local finite-free map, on every
   open and for every natural-number rank. This is 01BV, rather than the
   weaker upstream quasi-coherent-plus-finite-presentation predicate.
4. Both outputs in clause (1):
   `IsCoherent X (kernel f) ∧ IsCoherent X (cokernel f)`.
   Verdict: both present, using the categorical kernel and cokernel in the
   same sheaf-of-modules category. The source's constructions have those
   universal properties, so no sectionwise quotient is substituted for its
   sheafification.
5. Arbitrary short exact sequence in clause (2):
   `S : ShortComplex (SheafOfModules.{u} (moduleRings X))`, `S.ShortExact`.
   Verdict: exact. I read Mathlib `ShortComplex.ShortExact`: exactness plus
   `Mono S.f` and `Epi S.g` encode the two zero ends. No coherent term is
   assumed before the three alternatives are quantified.
6. Each choice of two coherent terms implies the third:
   `X₁ → X₂ → X₃`, `X₁ → X₃ → X₂`, and `X₂ → X₃ → X₁`, with
   `IsCoherent X` applied to each term. Verdict: all three alternatives are
   present, each with exactly its two coherence hypotheses, agreeing with
   01BY(4).
7. Clause (3), every finite list, with all entries coherent:
   `r : ℕ`, `F : Fin r → SheafOfModules.{u} (moduleRings X)`,
   `(∀ i : Fin r, IsCoherent X (F i)) → IsCoherent X (⨁ F)`.
   Verdict: exactly the list of r modules in the node. This is the categorical
   finite biproduct, hence their finite direct sum. The local instance is the
   existing Mathlib `HasFiniteBiproducts.of_hasFiniteProducts`, not an added
   mathematical hypothesis or a newly proved declaration.
8. Empty-list clause: `IsCoherent X (0 : SheafOfModules.{u} (moduleRings X))`.
   Verdict: explicitly present as well as covered by `r = 0`.
9. Isomorphism clause: `∀ F G (_e : F ≅ G), IsCoherent X F → IsCoherent X G`.
   Verdict: the arbitrary recipient of an isomorphism to a coherent module
   is coherent; reversing the isomorphism covers either stated orientation.

Edge cases checked: `Fin 0` is empty and the hypothesis on summands is
vacuous; its biproduct is zero, explicitly included. `r = 1` recovers the
single module up to isomorphism. Identity morphisms have zero kernel and
cokernel; zero morphisms between coherent modules have the expected source
kernel and target cokernel. Sequences with a zero term and split sequences
fit the three alternatives. Empty spaces and empty schemes are permitted.
There is no restriction on characteristic and no requirement that the
structure sheaf be nonzero. The bound universe `u` is the one used by the
recorded coherence definition and module carrier; finite lists introduce no
test-object universe or restriction on an index set. All variables are bound.

Independent searches used different wording from the first reading:

- LeanFinder: `kernel cokernel extension finite biproduct coherent O_X
  modules` returned eight results, including abelian categories of all
  modules, free-presentation data, and an abstract biproduct kernel lemma;
  none states Stacks-coherence closure.
- Loogle: `SheafOfModules, kernel` reported unknown identifier `kernel`;
  the valid follow-up `SheafOfModules.IsFiniteType` returned four finite-type
  or finite-presentation-definition results and no closure theorem.
- LeanSearch: `coherent sheaves closed under kernels cokernels extensions
  finite sums` was unavailable (Internal Server Error); this is recorded as
  unavailable, not evidence of absence.
- msearch grep: `coherent.*(kernel|cokernel|biprod|sum)|IsCoherent` returned
  nineteen mostly topological-coherence or quasi-coherence matches.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, and project
  `lean/Sheaf` for `IsCoherent`, `isCoherent`, `is_coherent`, and coherence
  near kernel/cokernel/sum found the recorded project definition and upstream
  quasi-coherent-kernel and locally-Noetherian finite-presentation results.
  I opened upstream `Modules/Coherent.lean:46` and
  `Modules/QuasicoherentKernel.lean:269`: the former explicitly defines the
  weaker predicate, and the latter requires `IsLocallyNoetherian X`.
  Neither replaces this theorem. Searches for the full declaration name and
  blueprint id in the upstream source/name table found no collision.

No mismatch was found and no Lean or node field needed changing. No new
definition node or dependency replacement is required. The module contains
one named theorem with `sorry`, no definitions or proved auxiliary results.
Its source-tagged docstring follows all seven DAG steps: preliminary local
facts, kernel, finite-type image/cokernel, the cokernel snake diagram, the
two kernel/cokernel exact-sequence cases, the extension snake diagram, and
induction on the finite sum. The namespace, imports, and line widths follow
the stated conventions. The recorded signature agrees verbatim with the
file (also checked with `stage2_delivery.py signature`).

Validation: `scompile.py` on the absolute sandbox module path compiled cleanly
in 2.1 seconds, exit 0, with no warnings. Changes from this reading: appended
this clause-by-clause review; retained the correct theorem and node.
Delivery dry run printed OK: preflight and compile both passed.
