## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel` states
`AlgebraicGeometry.coherentFormalModule_kernel`; its only theorem proof is `sorry`.
The original node is unchanged outside `lean`. No new notions or dependency modules
are needed. No statement dispute or correction is required.

Hypotheses and clauses:

- Noetherian scheme: `{X : Scheme.{u}} [IsNoetherian X]`. Mathlib's class extends
  `IsLocallyNoetherian X` and `CompactSpace X`, exactly the two stated conditions.
- Quasi-coherent ideal: `I : X.IdealSheafData`, the encoding used by the recorded
  coherent-formal-module dependency, with its canonical module inclusion `I.toModulesι`.
- Objects and morphism: `F H : CoherentFormalModule X I` and `α : F ⟶ H`.
  These are the shared full subcategory of coherent adic functors and its natural
  transformations. Positive paper level n is Lean `op (n - 1)`; thus throughout the
  statement `op n` denotes paper level n+1, with no level zero imposed.
- Sectionwise kernel and image K'_(l,m): `kernel.ι (α.hom.app (op l))` composed with
  `F.obj.map (homOfLE ...).op`, then `Abelian.image.ι`. Categorical module kernels
  are sectionwise; the recorded image theorem identifies abelian images with the
  stated local-image subsheaf. `Subobject.mk` compares inclusions as subobjects,
  rather than equating arbitrary chosen carrier objects.
- Clause (1): `∃ c : ℕ` is the nonnegative integer bound; the first conjunct, for all
  `l m` with `h : m + c ≤ l`, equates exactly these image subobjects with the image
  at `m+c`. `Nat.le_trans (Nat.le_add_right m c) h` supplies l ≥ m.
- The notation K'_m and clause (2)'s transition restriction are represented by
  `S : ℕᵒᵖ ⥤ X.Modules` and `j : S ⟶ F.obj`. For every m an isomorphism identifies
  `S.obj (op m)` with the stabilized abelian image; its composite with the image
  inclusion is `j.app (op m)`. In particular these components are monomorphisms.
  Naturality of j for every arrow expresses that all the transition maps of F
  restrict to the stated inclusions, including every m' ≥ m.
- Quotients K_n: `K : CoherentFormalModule X I` and the family `e` identify its
  n+1 level with `formalModuleQuotient I (n + 1) (S.obj (op (n + c)))`.
  This is precisely K'_(n+1+c)/I^(n+1)K'_(n+1+c). Membership in the recorded category
  includes coherence, annihilation, and the required reduction isomorphisms.
- Induced transitions: the first conjunct after e equates the two composites from
  S at index n+1+c to K at index n: quotient by I^(n+2) followed by K's transition,
  versus S's transition followed by quotient by I^(n+1). Since the quotient
  projection is epi, this characterizes the induced transition, not an arbitrary map.
- Clause (3)'s induced iota: `ι : K ⟶ F`, and the next displayed equation identifies
  its composite with the quotient projection with `j` followed by F's transition.
  This is exactly the map obtained by reducing the inclusion into F_(n+1+c) and
  identifying its reduction with F_(n+1). The epi quotient characterizes it uniquely.
  Using that composite avoids choosing an arbitrary higher-level reduction iso.
- Morphism compatibility is built into `ι : K ⟶ F`. Zero composite is `ι ≫ α = 0`;
  the universal property is `∀ T γ, γ ≫ α = 0 → ∃! δ, δ ≫ ι = γ`.
  Lean composition is in diagram order, reversing the paper's circle notation.
  No component of iota is required to be mono: the parenthetical caveat is respected.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  with its exact Noetherian strengthening `AlgebraicGeometry.IsNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `CoherentFormalModule`,
  `IsCoherentFormalModule`, `formalModuleQuotient`, `formalModuleQuotientπ`.
  Read their full declarations and docstrings: the object predicate has all three
  coherence/annihilation/induced-isomorphism conditions, at positive levels.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`:
  `AlgebraicGeometry.Scheme.Modules.quasiCoherent_cokernel_image`. Its full signature
  and docstring identify `Abelian.image` with the local-image subsheaf, and record
  quasi-coherence and affine range formulas. This import supplies the image API.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `AlgebraicGeometry.Scheme.Modules`,
  definition as `SheafOfModules`, with its abelian and limit instances.

Edge cases: c=0 is allowed, and l=m is included when appropriate. The smallest
positive level is represented by index 0, with ideal exponent 1; the empty scheme,
zero systems, zero morphisms, unit ideal and zero ideal are not excluded. One
scheme universe suffices for the same module category as the dependency. The
image comparison uses subobjects to avoid demanding equality of chosen image
carriers; the quotient and inclusion equations retain the actual maps.

Searches for reuse:

- `msearch.py ... leanfinder "Images of levelwise kernels in coherent adic inverse
  systems stabilize and their reductions form the categorical kernel"`: eight hits,
  including AdicCompletion.kerProj_of, ModuleCat.kernelIsLimit, Hausdorffification,
  and localCohomology; none states this coherent formal system theorem.
- `msearch.py ... loogle "CategoryTheory.Limits.kernel, CategoryTheory.Abelian.image"`:
  twelve general abelian-image/coimage hits; no adic-system stabilization theorem.
- `msearch.py ... grep "CoherentFormalModule|coherentFormalModule_kernel"`: zero
  Mathlib hits.
- `rg` of the source `WeilConjectures` for the item id, CoherentFormalModule and the
  chosen name: no hits. `rg` of `dag/lean_names_upstream.json` and `lean/Sheaf` for
  the item id and chosen name: no existing theorem. The broader project search
  identifies the existing CoherentFormalModule dependency, which is reused.

Source checked: the local literature file is absent on this machine, so read the
actual Stacks proof at https://stacks.math.columbia.edu/tag/087X. Its four claims and
Artin--Rees quotient formula agree with the node. The node supplies the expanded
uniqueness proof, which is included along with its other five proof steps in the
Lean docstring.

Validation: server single-file compilation is clean (only the expected sorry is
present). The delivery dry run is run after writing this report. The independent
second reading is reserved for the next worker.

## Second reading by J1

Independent reading of the node, its four statement dependencies, and the complete
Lean module. I fetched the Stacks `coherent.tex` into sandbox scratch and read
Section `section-coherent-formal` and the proof of
`lemma-inverse-systems-abelian` (087X), including claims (a)--(d). The standing
hypotheses are exactly Noetherian X and a quasi-coherent ideal; no properness,
separatedness, base ring, or completeness hypothesis on X is imposed.
Source: https://stacks.math.columbia.edu/tag/087X and
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

1. X is a Noetherian scheme: `{X : Scheme.{u}} [IsNoetherian X]`.
   Read Mathlib's `IsLocallyNoetherian` and `IsNoetherian` declarations; the
   latter extends the former and `CompactSpace X`, precisely the locally
   Noetherian plus quasi-compact condition. No extra geometric hypothesis.
2. The quasi-coherent ideal I: `(I : X.IdealSheafData)`. Read Mathlib's
   `IdealSheafData` affine ideals and basic-open localization condition and the
   source's `toModulesι` kernel inclusion. These describe the same ideal sheaf,
   including non-finite-type ambient schemes; here Noetherian X is already given.
3. Two coherent formal systems and a compatible linear morphism:
   `(F H : CoherentFormalModule X I) (α : F ⟶ H)`. Read the recorded
   `CoherentFormalModule`, `IsCoherentFormalModule`, and full-subcategory
   declarations. They require coherence, annihilation by I^(n+1), and the
   transition-induced quotient isomorphism. Morphisms are natural
   transformations. Paper level p≥1 is Lean `op (p-1)` throughout.
4. For l≥m≥1, the sectionwise kernel and its image in F_m:
   `kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE ...).op`, inside
   `Abelian.image.ι`. Read the recorded `Scheme.Modules` definition, its
   abelian/limit instances, and the entire `quasiCoherent_cokernel_image`
   signature and docstring. The abelian image is the local-image subsheaf,
   not the possibly non-sheaf sectionwise range. The kernel is categorical
   in all O_X-modules, not a kernel in the formal category.
5. One common nonnegative bound c: `∃ c : ℕ`, before every later quantifier.
   Clause (1) is the first `∀ l m h` equality of `Subobject.mk` images,
   with `h : m+c ≤ l`. Both images have target F at `op m`. The proof terms
   only construct the requisite order arrows; they add no assumptions.
   Equality of subobjects is precisely equality of included image sheaves,
   without demanding equality of arbitrary chosen carrier representatives.
6. Stabilized K'_m and restricted transitions, clause (2): `∃ S j` and the
   `∀ m, ∃ e` isomorphism to the stabilized image with
   `e.hom ≫ Abelian.image.ι ... = j.app (op m)`. Each j component is thus
   mono. Naturality of `j : S ⟶ F.obj` states that every transition F_m'→F_m
   restricts to S_m'→S_m, for all m'≥m. There is no extra coherence condition
   on S; its identification with the stated images supplies the intended data.
7. Quotient levels and membership, clause (2): `∃ K : CoherentFormalModule X I`
   and `e n : formalModuleQuotient I (n+1) (S.obj (op (n+c))) ≅ K.obj.obj (op n)`.
   Read `formalModuleQuotient` as the cokernel of the shared ideal-product
   inclusion for I^(n+1), and its projection `formalModuleQuotientπ`.
   Thus Lean level n is paper K_(n+1) = K'_(n+1+c)/I^(n+1)K'_(n+1+c).
   Formal-category membership includes all three required object conditions.
8. Induced adjacent transitions: the first equation after the e family compares
   projection at exponent n+2 followed by e(n+1) and K's transition with S's
   transition followed by projection at exponent n+1 and e(n). The source
   index is `op (n+1+c)` and the target index is `op n`; these match exactly.
   The cokernel projection is epi, so this equation specifies the induced map.
9. Induced inclusion maps, clause (3): `ι : K ⟶ F` and the next `∀ n` equation
   identifies quotient projection followed by e(n) and iota with j at n+c
   followed by F's transition to n. This is precisely the reduction of the
   inclusion K'_(n+1+c) into F_(n+1+c). It uses the actual transition, and
   hence the reduction isomorphism supplied by F's object conditions.
10. Compatibility, zero composite and kernel universal property, clause (3):
    `ι : K ⟶ F` already gives compatibility;
    `ι ≫ α = 0` and `∀ T γ, γ ≫ α = 0 → ∃! δ, δ ≫ ι = γ`
    give exactly existence and uniqueness of every factorization. Composition
    is in diagram order. There is no assertion that any iota component is mono,
    respecting the node's caveat about termwise injectivity.

Edge cases: c=0, l=m, the smallest positive level (Lean n=0, exponent 1),
zero systems, zero morphisms, the empty scheme, and zero/unit ideals are all
allowed. There is no empty-index-set hypothesis: the fixed positive-level
index is ℕᵒᵖ. Characteristic is unrestricted. `u` is bound and arbitrary;
the module universe is that of the recorded category, with no quantified test
objects in a smaller independent universe. No variable is auto-implicit.

Independent reuse searches, with different keywords from the first worker:

- LeanFinder via msearch: "Kernel of morphism between coherent formal sheaves
  via eventual stable images and Artin Rees"; eight ideal-sheaf kernel hits,
  concerning kernels of scheme morphisms, not coherent formal systems.
- Loogle via msearch: "AdicCompletion"; twelve completion object/operation hits,
  none the geometric stabilization and kernel construction here.
- Grep via msearch: "inverse.*system.*kernel|kernel.*inverse.*system|CoherentFormal";
  zero hits.
- Direct rg on source WeilConjectures, project lean/Sheaf, and Mathlib's
  AlgebraicGeometry and RingTheory/AdicCompletion directories for formal/kernel,
  stabilization/image, eventually/image, the item id, and declaration name.
  Only unrelated Fourier, rigidity, Mittag-Leffler and convergence occurrences;
  no existing declaration of this statement. The shared formal-category,
  quotient, image and sheaf-module notions are reused, not copied.

There are no new definition nodes or dependency modules in this delivery.
The sandbox node differs from the repository node only in `lean`; its signature
matches the file verbatim. No statement correction or dispute is present.
The theorem docstring follows all five node proof steps: affine reduction,
Artin--Rees stabilization, quotient-system construction, factorization existence,
and uniqueness without termwise injectivity. Imports supply the shared category
and quotient definitions and the abelian-image API. No hollow definitions,
private conventions, hidden let/show binders, or proved theorems occur; the sole
proof is `by sorry`.

Mismatches found: none. Changes: appended this independent second reading;
Lean and node left unchanged. Single-file server compilation and delivery
preflight are checked before delivery.
