## Worker report

The module `Sheaf.Algebra.Homology.ModuleStalkExact` states
`AlgebraicGeometry.RingedSpace.module_stalk_exact`.  It uses the existing
`SheafOfModules` category over the structure sheaf of a `RingedSpace` and the
existing `RingedSpace.moduleStalkFunctor`; no new mathematical definition is
introduced.  A scheme is covered by viewing it as its underlying ringed space.

The first conjunct renders clause (1): for every open `U`, the concrete map
`φ.val.app (Opposite.op U)` is injective.  The second conjunct renders clause
(2): at every point, the stalk map of `kernel.ι φ` is mono and the short complex
`stalk(Ker φ) → stalk(F) → stalk(G)` is exact.  The third renders clause (3):
the stalk map of `cokernel.π φ` is epi and the short complex
`stalk(F) → stalk(G) → stalk(Coker φ)` is exact; in `ModuleCat` this is the
canonical cokernel and therefore expresses the induced quotient isomorphism.
The fourth renders clause (4): the stalk map of the canonical image
factorization is epi, the stalk image inclusion is mono, and its composite with
the stalk cokernel map is exact, expressing that the stalk image is the kernel
of the stalk cokernel.  The final conjunct renders clause (5): for every
complex `χ, ψ` with `χ ≫ ψ = 0`, `ShortComplex.Exact` is equivalent to exactness
of every mapped stalk short complex.

Dependency declarations used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` (the scheme is handled
  through its underlying ringed space).
- `def-weil-sheaf-of-modules-category`: Mathlib `SheafOfModules` and its
  `SheafOfModules.instAbelian` instance.
- `def-weil-pbc-module-stalk`: Mathlib `TopCat.Presheaf.stalk` and the module
  structure from `Mathlib.Algebra.Category.ModuleCat.Stalk`.
- `def-weil-pbc-exact-sequence`: Mathlib `CategoryTheory.ShortComplex.Exact`.

The edge cases checked were empty opens and empty spaces (the universal
quantifiers are vacuous), zero morphisms and zero objects (the short-complex
zero proofs reduce by `map_comp` and simp), and arbitrary universe `u` for the
ringed space and its stalk modules.  The stalk functor uses the same universe
as the ringed space, so no independent smaller test universe is introduced.

Searches made before writing: `msearch.py leanfinder` for stalk kernel/cokernel
exactness (only `ModuleCat.Tilde` stalk lemmas; no match), `msearch.py loogle`
for `SheafOfModules` stalk exactness (no match), `msearch.py grep` in Mathlib
for stalk exactness and finite-colimit preservation (only the abelian-valued
sheaf theorem, no module-sheaf theorem), `rg` in `WeilConjectures` and the
project `lean/Sheaf` for module-stalk exactness (no existing declaration), and
`grep` for the target id (only this node and downstream textual references).
The existing `RingedSpace.moduleStalkFunctor` was inspected and imported.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Earlier second reading (a previous round; superseded)

The recorded declaration, imports, and signature were re-read after compilation.
The four stalk assertions use the canonical kernel, cokernel, image factorization,
and image inclusion in the abelian `SheafOfModules` category; the final assertion
uses `ShortComplex.Exact` and the mapped stalk short complexes.  The dry-run
reader should verify the equivalence of these categorical formulations with the
five prose clauses.

## Second reading by H1

Read independently with the node, the complete Lean module, each of its four
statement-dependency records and their declarations open. The source checkout
has no local `literature/stacks-project/modules.tex`; read the actual Stacks
`modules.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/modules.tex,
lines 59–172 (`section-kernels`, Tag 01AF; `lemma-abelian`, Tag 01AG).
The source assumes only a ringed space and arbitrary sheaves of modules. There
is no separatedness, Noetherian, finiteness, locality or field hypothesis.

Object/hypothesis/conclusion inventory and final Lean match:

1. X is a scheme, or more generally a ringed space: `(X : RingedSpace.{u})`.
   Mathlib `Scheme` extends `LocallyRingedSpace`, hence gives its underlying
   ringed space. Verdict: the general case requested, including schemes.
2. Mod(O_X) and arbitrary module sheaves F,G, with a module-sheaf morphism φ:
   `{F G : SheafOfModules.{u} (moduleRings X)} (φ : F ⟶ G)`.
   Read `SheafOfModules` and `Hom` in ModuleCat/Sheaf.lean, and the Mathlib
   abelian instance in Sheaf/Abelian.lean. This is a sheaf of abelian groups
   with sectionwise module structure and semilinear restrictions; morphisms
   are sectionwise linear. `moduleRings` (DerivedHomMayerVietoris.lean:34)
   merely views the existing commutative structure sheaf as a ring sheaf.
   Verdict: exactly the dependency notion, with the existing abelian instance.
3. Points x and O_{X,x}-module stalks and induced maps: `∀ (x : X)` and
   `(moduleStalkFunctor X x).map`. Read the complete ModuleStalkFunctor module:
   its object is the abelian-presheaf stalk with the Mathlib module instance,
   and its map is the induced additive stalk map equipped with linearity.
   Read the instances and `germ_ringCat_smul` in ModuleCat/Stalk.lean:167–199.
   Verdict: the dependency's actual stalk and module action, no new stalk notion.
4. k, c, image, inclusion and factorization are the canonical maps
   `kernel.ι φ`, `cokernel.π φ`, `Abelian.image.ι φ`, and
   `Abelian.factorThruImage φ`. Read Abelian/Images.lean:47–59: the latter
   image is literally `kernel (cokernel.π φ)`, with its kernel inclusion.
   Canonical categorical choices are allowed by node proof step 0; the
   assertions transport along the unique compatible isomorphisms.
   Verdict: same objects and structure maps.
5. Clause (1), and its only conditional hypothesis: final first conjunct is
   `(∀ U, Function.Injective (ConcreteCategory.hom (φ.val.app (op U)))) →
   ∀ x, Mono ((moduleStalkFunctor X x).map φ)`.
   `ModuleCat.mono_iff_injective` (EpiMono.lean:43) identifies the conclusion
   with injectivity of φ_x. Verdict: repaired; the original first conjunct
   asserted sectionwise injectivity unconditionally and omitted its consequence.
   In particular a zero map from a nonzero module sheaf refuted the original.
6. Clause (2): second conjunct is `∀ x, Mono (stalk(k)) ∧ Exact(stalk(k),stalk(φ))`.
   Read `ShortComplex.Exact` and `ShortComplex.exact_iff_image_eq_kernel`;
   exactness says image(k_x)=kernel(φ_x). Verdict: precisely injectivity and
   the required kernel image; no extra assumption on φ.
7. Clause (3): third conjunct is `∀ x, Epi (stalk(c)) ∧ Exact(stalk(φ),stalk(c))`.
   `ModuleCat.epi_iff_surjective` (EpiMono.lean:50) says c_x is surjective;
   exactness says its kernel is the image of φ_x. The induced canonical
   O_{X,x}-linear map from G_x/image(φ_x) is consequently an isomorphism,
   and conversely that quotient isomorphism gives these assertions.
   Verdict: equivalent to both the surjection/kernel and induced-isomorphism clauses.
8. Clause (4): fourth conjunct is `∀ x, Epi (stalk(factorThruImage φ)) ∧
   Mono (stalk(image.ι φ)) ∧ Exact(stalk(image.ι φ),stalk(c))`.
   By functoriality the composite of the first two maps is φ_x; surjectivity
   of the first and injectivity of the second identify the stalk image with
   image(φ_x) inside G_x. Exactness with c_x adds nothing stronger: by clause
   (3) this kernel is already image(φ_x). Conversely the node's clause (4)
   and clause (3) give this exactness. Verdict: same conjunction as the node.
9. Clause (5): final conjunct quantifies arbitrary H, χ:F→G, ψ:G→H and
   `h : χ ≫ ψ = 0`, and asserts
   `(ShortComplex.mk χ ψ h).Exact ↔ ∀ x, ((ShortComplex.mk χ ψ h).map
   (moduleStalkFunctor X x)).Exact`. F,G are already universally quantified
   and φ imposes no assumption, so every three-term complex is covered.
   The composition-zero binder is precisely the complex condition, and
   `ShortComplex.Exact` is the recorded dependency's middle exactness.
   Verdict: both directions, every point, correct quantifier order.

Edge cases: no points are assumed to exist; on an empty space all stalk
quantifiers are vacuous and the module-sheaf category is the zero category,
so clause (5) correctly says all complexes are exact. The empty open is
included in `∀ U`; sheaf sections there are zero. Zero objects and zero
morphisms are allowed; clause (1) is now conditional, so it no longer asserts
injectivity for a zero map from a nonzero object. No index set or integer n
is introduced; n=0 does not apply. Structure rings may have any characteristic
and may be zero. `universe u` is arbitrary, with the same module/stalk universe
as the landed stalk functor; larger carriers can be accommodated by raising
the common universe. No independent smaller universe or extra instance binder
makes any hypothesis vacuous.

Independent searches used alternative wording:

- `msearch.py ... leanfinder "kernel and cokernel of sheaves of modules commute
  with stalks"`: eight hits, all tilde sheaves on an affine spectrum or smooth
  manifold sheaves; no declaration for these arbitrary module sheaves.
- `msearch.py ... loogle 'SheafOfModules, "stalk"'`: zero hits.
- `msearch.py ... grep 'stalkFunctor.*(exact|Exact)|exact_iff_stalk|stalk.*cokernel'`:
  only the constant-value abelian-sheaf result in Topology/Sheaves/Abelian.lean.
  Read its theorem at line 103: its source category is `Sheaf C X`, rather
  than `SheafOfModules` over a varying structure sheaf. It is not this statement.
- `msearch.py ... leansearch "sheaves of modules over a ringed space preserve
  kernels and cokernels on stalks"`: unavailable (HTTP Internal Server Error);
  no verdict is inferred from the unavailable service.
- Independent `rg` over Mathlib ModuleCat/Sheaf and Topology/Sheaves, and over
  all project `lean/Sheaf` and source `WeilConjectures` for stalk/exactness,
  `module_stalk_exact`, module encodings and the name index: no existing
  statement. Geometric Weil-sheaf stalk exactness is a different setting.
  The project search found the usable existing `AlgebraicGeometry.moduleRings`.

Mismatches and repairs: fixed clause (1) as above; removed the undocumented
public `RingedSpace.Modules` abbreviation and directly reused
`SheafOfModules (moduleRings X)`, importing its existing project module;
added the standard copyright/license header and the missing module docstring;
expanded the theorem docstring to all proof steps 0–8, including the named
sheafification and local-lifting dependencies. Updated `lean.statement` to the
verbatim multiline signature in the file. Kept all other node fields and
clauses (2)–(5) unchanged. No new nodes, dependency modules or node statement
correction are needed. There are no hollow definitions; the single theorem
proof is `sorry`, with only composition-zero checks inside its signature.
Every variable and universe is bound; all lines are at most 100 characters.

Validation: final `scompile.py H1 lem-weil-pbc-module-stalk-exact` compiled the
module on the server in 2.3 seconds, exit 0, with no warnings or errors.
