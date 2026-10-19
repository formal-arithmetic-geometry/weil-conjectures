## Worker report

The module `Sheaf.Paper.RingComplexFunctorial` states
`AlgebraicGeometry.exists_functorial_ringComplex`. Its only theorem has proof `sorry`.
It introduces no definitions and makes no change to the mathematical statement or proof
of the node. The source was read directly in `literature/stacks-project/algebraization.tex`,
`lemma-all-rings` (Tag 099D), especially clauses (a)-(d). The declaration docstring contains
all six steps of the node's recorded proof, including the replacement Godement construction,
the finite augmented Cech roof, and the arbitrary-base-change fraction calculation.

The statement is a single joint existence assertion: the family K, augmentations, and
semilinear maps are chosen together, before their compatibility properties. It does not
choose unrelated complexes separately for each map.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Every commutative ring A | `A : CommRingCat.{u}`; the universe u is arbitrary. |
| Finitely generated ideal I | `I : {I : Ideal A // I.FG}`. |
| A complex K(A,I) of A-modules | `K A I : CochainComplex (RingSiteModules A) ℤ`. |
| Modules on the one-object site | The existing `CategoryTheory.RingSiteModules` uses `SheafOfModules` over `CochainComplex.onePointRingSheaf A`, on `Discrete PUnit` with bottom topology. This is the specialization of the recorded general ringed-site module category, with no new module category. |
| Augmentation K(A,I) to A[0] | The actual complex morphism `ε A I` lands in `HomologicalComplex.single ... (ComplexShape.up ℤ) 0` of the rank-one module `SheafOfModules.unit`. |
| Every ring map φ:A to B | `φ : A →+* B`, with no flatness, Noetherianity, or other restriction. |
| Target ideal IB | `J` is a finitely generated ideal with `h : I.val.map φ = J.val`. Extension of an FG ideal is FG, so such a J always exists, and all J satisfying this equality are quantified over. This formulation avoids transports along ideal-map composition equalities. |
| φ-linear chain map | `m A B φ I J h n` is a semilinear map `→ₛₗ[φ]` on the unique object's sections in every degree. The first conjunct is its differential-commutation equation for every pair of integer degrees. On this one-object category these are precisely semilinear maps of the module-sheaf complexes. |
| Compatible with augmentations | The second conjunct is `ε_B(m(x)) = φ(ε_A(x))` in degree zero. `singleObjXSelf` supplies the canonical identification of the single complex's zero term with A. In every other degree the augmentation target is zero, so the corresponding square is uniquely determined. |
| Identity and composition | The third conjunct says the identity ring map acts identically; the fourth says `m ψ (m φ x) = m (ψ.comp φ) x`, with all three extended-ideal equalities explicit. The node proof explicitly includes identity as well as composition. |
| Induced derived base change | The fifth conjunct quantifies over every `p : P ⟶ K A I` with `P.IsKFlat` and `QuasiIso p`. It gives a B-module complex E with termwise isomorphisms to `SheafOfModules.changeOfRings (ringSiteMap φ) (P.X n)` and specifies the differential by conjugating `changeOfRingsHom`. Thus E is exactly scalar extension of P as a complex, up to its specified term isomorphisms. The map `χ : E ⟶ K B J` sends the image of `1 ⊗ x`, through the actual sheafification unit and `t.inv`, to `m φ (p x)`. B-linearity determines χ on all pure tensors, and the one-object bottom-topology sheafification unit is invertible. Consequently this is the induced map, not an arbitrary isomorphism between its endpoints. `IsIso (DerivedCategory.Q.map χ)` is the asserted isomorphism in D(B). |
| Derived tensor convention | Scalar extension of P is the total tensor with B concentrated in degree zero: in total degree n its only nonzero summand is B tensor P^n, and its differential is `1 tensor d_P`. The explicit E, t, and differential equations specify precisely that complex, with the B action on the first factor. Symmetry of tensor over the commutative ring identifies this with the node's P tensor B convention. The K-flat condition is the dependency's literal `CochainComplex.IsKFlat`, defined using the total tensor `CochainComplex.mapBifunctor`, rather than a substitute K-flat predicate. `lem-pc-kflat-resolution` ensures that the quantified replacements exist on this site. |
| A finite generating list, including r=0 | `r : ℕ`, `f : Fin r → A`, and `Ideal.span (Set.range f) = I.val`. There is no nonempty assumption on `Fin r`. |
| The localization complex C_A(f) | The last conjunct gives C with all term coordinates, differentials, and augmentation specified. These coordinates specify the named localization complex up to its unique coordinate-preserving complex isomorphism; C is not left as an unconstrained complex with the same cohomology. |
| Degree zero equals A | `e₀ : (C.X 0).val.obj ... ≃ₗ[A] A`. |
| Degree q>0 equals the ordered finite localization product | `e q` identifies degree q+1 with the product over `Fin (q+1) ↪o Fin r` of `Localization.Away (∏ i, f (t i))`. Order embeddings are exactly strictly increasing lists. |
| All other degrees are zero | Negative terms satisfy `IsZero (C.X n)`. For q+1>r there are no order embeddings, so the positive-term coordinate product is the zero module. Evaluation detects zero objects on this identity-only one-object site. |
| Localization at powers | `Localization.Away g` is Mathlib's localization at `Submonoid.powers g`. |
| Alternating localization differential | The first differential sends x to its algebra-map images in each singleton coordinate. For higher differentials the equation is the sum over deleted positions j, with sign `(-1 : ℤ)^j.val`; `(Fin.succAboveOrderEmb j).trans t` deletes that position. Each `l q t j` is an A-algebra hom between the specified localizations. The universal property of localization makes every such A-algebra hom the unique canonical localization map; no arbitrary coefficient map is substituted. |
| Augmentation of C is identity in degree zero | The equation for `a.f 0`, after `singleObjXSelf`, is exactly `e₀ x`. All other components have zero target automatically. |
| Augmentation-compatible isomorphism in D(A) | `α : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj (K A I)` with `α.hom ≫ DerivedCategory.Q.map (ε A I) = DerivedCategory.Q.map a`. |

The instance family `[∀ A, HasDerivedCategory.{w} (RingSiteModules A)]` is precisely the
chosen-localization-universe convention of `def-weil-abstract-derived-category`. It adds
no ring-theoretic hypothesis; the standard localization is available in a sufficiently
large universe. All universes and variables are bound, and `autoImplicit` is disabled.
There are no `let`, `have`, file-local notation, local instances, or private declarations
in the module. The explicit `@id` casts use an already specified module type.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, and `HasDerivedCategory.standard` (the existing localization).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the transparent
  abbreviation for Mathlib's `SheafOfModules` on any ringed site; its underlying definition
  is the one used by `RingSiteModules`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the total tensor
  used by the recorded K-flat definition and by tensor with a complex in degree zero.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat` and `IsKFlatResolution` were read;
  the statement uses `P.IsKFlat` and `QuasiIso p` directly.
- `Sheaf.Algebra.Homology.KFlatResolution`: `CochainComplex.exists_isKFlatResolution`,
  imported as a proof dependency, ensures existence of replacements with no extra hypothesis.
- `Sheaf.Algebra.Homology.RingHomExtensionDefs`: existing `CategoryTheory.RingSiteModules`
  and `CategoryTheory.ringSiteMap`. The already-landed node
  `def-pc-ring-hom-extension-shared-definitions` is added to `stmt_deps` to cite these shared
  interfaces. No dependency module is replaced or copied.
- Mathlib's `SheafOfModules.unit`, `HomologicalComplex.single`, and `singleObjXSelf` provide
  the coefficient complex and its canonical zero-degree identification.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: existing
  `SheafOfModules.changeOfRings`, `changeOfRingsPresheaf`, and `changeOfRingsHom` specify
  scalar extension and its differential; `CategoryTheory.toSheafify` is its actual unit.

Every proof dependency with a recorded module (or a Mathlib match) is imported. The only
proof dependency without a recorded declaration,
`lem-weil-pbc-finite-ordered-flasque-cech-comparison`, has no module to import; its use is
retained in the theorem's proof docstring for stage 3. It is not a statement dependency.

Edge cases checked by reading the full formulas:

- r=0 forces I=0; all positive localization products are over empty index types, negative
  terms are zero, and the zero-degree augmentation identifies C with A[0].
- Zero ring A or B is allowed. Localizing at zero is the zero ring, not an excluded case.
  An A-algebra map from a zero localization exists here exactly because the target
  denominator contains the deleted denominator as a factor.
- Repeated generators and zero generators do not change the tuple indexing or sign rules.
- I=A is allowed; the complex can be acyclic, with no nonvanishing conclusion imposed.
- Identity and composite maps include nonflat maps and maps killing a denominator.
- K and the K-flat replacement are unbounded integer-indexed complexes. No boundedness
  or term-flatness hypothesis is added to the assertion.

Searches for an existing statement:

- `msearch.py leanfinder`, query “Functorial augmented local cohomology complex for finitely
  generated ideals compatible with arbitrary ring base change”: eight fixed-ring
  `localCohomology` namespace results, including `localCohomology`, `.diagram`, `.ofDiagram`,
  `.ofSelfLERadical`, `.ringModIdeals`, and `.idealPowersDiagram`; no exact match.
- `msearch.py loogle`, query `"localCohomology"`: twelve fixed-ring declarations and category
  instances; no jointly ring-varying augmented complex or the requested base-change theorem.
- `msearch.py grep`, query `Cech|localCohomology|extendedCech`, subdirectory `Algebra/Homology`:
  five hits in `LocalCohomology.lean`. The file describes the Cech characterization as future
  work and constructs local cohomology from Ext colimits; it is not this statement.
- `msearch.py leansearch`, query “Functorial augmented local cohomology complex for finitely
  generated ideals with arbitrary base change”: service unavailable, Internal Server Error.
- Direct `rg` of the upstream `WeilConjectures` tree and project `lean/Sheaf`, query
  `ringComplex|ring_complex|extendedCech|lem-weil-pbc-ring-complex-functorial|localCohomology`:
  only scheme-specific extended-Cech cycle maps and an unrelated local-cohomology tensor
  instance; no exact statement. Further `ringSite` searches found and reused the existing
  `RingSiteModules`/`ringSiteMap` definitions.
- Direct search for `exists_functorial_ringComplex|RingComplexFunctorial` in Mathlib, upstream
  sources, project sources, and `dag/lean_names_upstream.json`: no collision.
- The existing affine Koszul/Cech and affine alternating-Cech nodes were inspected. They are
  fixed-ring or scheme-cover comparisons, not Tag 099D's simultaneous functorial construction.

Validation: the delivered module compiled cleanly through `scompile.py` on the server,
nice 19, two threads, 60 seconds per file (the final compile took about three seconds).
Separate dependency-import probes also compiled. No local compiler or Lake build was run.
No statement dispute, correction, new definition node, or dependency replacement was needed.

## Second reading by NZ

I independently read the node, its six proof steps, the delivered theorem, and
`algebraization.tex`, `lemma-all-rings` (Tag 099D), including the complete proof and
its surrounding context. The source quantifies over arbitrary commutative rings and
finitely generated ideals; the finite-type rings in its proof are an intermediate
construction, not hypotheses on the statement. No statement correction is needed.

The following is my object/hypothesis/conclusion inventory, matched against the Lean.
Each row passes.

| Node item | Lean rendering and verdict |
| --- | --- |
| All commutative rings A | `A : CommRingCat.{u}`, arbitrary `u`; no characteristic, Noetherianity, or domain assumption. |
| Finitely generated ideal I | `{I : Ideal A // I.FG}`; precisely the stated hypothesis. |
| One family of complexes | The outer existential `K : ∀ A, {I // I.FG} → CochainComplex (RingSiteModules A) ℤ` chooses all objects before any ring-map compatibility. |
| A-modules, on the recorded one-object site | `RingSiteModules` unfolds to `SheafOfModules` of the constant ring sheaf on `Discrete PUnit` with bottom topology. Evaluation is the ordinary A-module category: the site has one object and only identity arrows. |
| Augmentation to A[0] | The jointly chosen `ε` lands in `HomologicalComplex.single ... 0` of `SheafOfModules.unit`, whose unique section module is A. |
| Every ring map A → B, with ideal IB | `φ : A →+* B`, `J`, and `h : I.val.map φ = J.val`. Ideal extension preserves finite generation, so this quantification omits no ring map. Proof irrelevance removes dependence on the equality witness. |
| Semilinear chain map | `m ... n : ... →ₛₗ[φ] ...`, with the first conjunct commuting with every `d n k`; on this site this is exactly a semilinear chain map. |
| Augmentation compatibility, source (a) | The second conjunct is `ε_B(m x) = φ(ε_A x)` in degree zero using `singleObjXSelf`. In all other degrees the target is zero, so there is no missing square. |
| Composition, source (b) | The fourth conjunct is the actual pointwise composite `m ψ (m φ x) = m (ψ.comp φ) x` for all extended-ideal witnesses. The third conjunct records identities, explicitly included in node proof steps 2 and 3. |
| Induced derived base change, source (c) | For every K-flat quasi-isomorphism `p : P ⟶ K A I`, the fifth conjunct specifies E termwise by isomorphisms `t` to the existing scalar extension and conjugates its differential by `changeOfRingsHom`. The chain map χ satisfies its pure-tensor normalization and `IsIso (DerivedCategory.Q.map χ)`. This fixes the induced map, not merely an unrelated isomorphism of endpoints. |
| Meaning of derived tensor | `P.IsKFlat` is the dependency's literal total-tensor acyclicity predicate. Extension is B tensor P with B concentrated in degree zero; its differential is `1 tensor d`. The symmetric commutative-ring tensor identifies this with P tensor B. On the bottom-topology site sheafification has invertible unit, so tensors `b tensor x` are generated by B-multiples of the stated `1 tensor x` normalization. |
| Every finite generating list | The final conjunct has `r : ℕ`, `f : Fin r → A`, and `Ideal.span (Set.range f) = I.val`, with no nonempty requirement. |
| Degree-zero localization term | `e₀` identifies the unique sections of `C.X 0` with A by an A-linear equivalence. |
| Positive localization terms | `e q` identifies degree q+1 with the product indexed by `Fin (q+1) ↪o Fin r` of `Localization.Away (∏ i, f (t i))`. Increasing embeddings give exactly the strictly increasing tuples. |
| Localization at powers | Mathlib's `Localization.Away` is the localization at the powers submonoid, including localization at zero. |
| Zero terms otherwise | Negative terms satisfy `IsZero`; above r the coordinate index type is empty, hence its product is the zero module. Evaluation on the unique object detects zero objects. |
| Alternating localization differential | The first equation is the localization map from A; the second uses signed deletion of entry j via `Fin.succAboveOrderEmb`. Each existential `l q t j` is an A-algebra map between these specified localizations, hence uniquely the canonical localization map by the localization universal property. No unspecified linear differential remains. |
| Localization augmentation | The equation on `a.f 0` is identity under `e₀` and `singleObjXSelf`; other components uniquely map to zero. |
| Augmentation-compatible derived comparison, source (d) | `α : Q.obj C ≅ Q.obj (K A I)` and `α.hom ≫ Q.map (ε A I) = Q.map a` are exactly the source's commuting derived diagram with identity on A. |

I opened the recorded statement-dependency declarations, not just their names:
`ringedSiteModules`, `RingSiteModules`, `ringSiteMap`, `onePointRingSheaf`,
`DerivedCategory`, `HasDerivedCategory`, `Q`, `mapBifunctor`, `IsKFlat`, and
`exists_isKFlatResolution`. I also read the actual `changeOfRingsPresheaf`,
`changeOfRings`, and `changeOfRingsHom` constructions: their terms are extension
of scalars and their maps are `id tensor a` followed by sheafification. These are
usable at precisely the site's universes. The chosen-localization family
`[∀ A, HasDerivedCategory.{w} (RingSiteModules A)]` implements the recorded size
convention; `HasDerivedCategory.standard` supplies a common sufficiently large w.
It is no added algebraic condition. There are no new nodes or dependency modules
in this delivery. The added dependency on the already recorded shared ring-site
interfaces is appropriate and avoids a duplicate construction.

Edge cases: r=0 gives I=0 and C=A[0], since every positive tuple type is empty.
Degree zero and all negative integer degrees are explicitly covered. The zero ring,
I=A, repeated and zero generators, arbitrary characteristic, nonflat maps, and maps
killing a denominator are all included. When a denominator becomes zero its
localization is zero, and the localization universal property still applies. The
empty scheme occurs only in the recorded proof (the complement for I=0), not as
an excluded scheme hypothesis. No boundedness of K or P is assumed. Universes u
and w are bound; using one universe u for the rings and modules is the customary
arbitrary size level, and rings of different sizes can be lifted into a common one.

Independent searches, with different wording from the worker's:

- `msearch.py leanfinder`: "augmented Cech complex for an ideal natural under ring
  homomorphisms" returned fixed-ring local-cohomology and adic quotient transition
  constructions, not this joint functorial existence theorem.
- `msearch.py loogle`: `"Cech"` returned Cech nerve declarations and unrelated name
  matches, not the augmented ideal-localization complex or Tag 099D.
- `msearch.py leansearch`: "augmented localization complex for a finitely generated
  ideal, natural in commutative rings" was unavailable (Internal Server Error).
- Direct `rg` for extended/alternating Cech, `099D`, `ringComplex`, and
  `localCohomology` in Mathlib homology, upstream `WeilConjectures`, project
  `lean/Sheaf`, and the proper-base-change DAG found no exact existing theorem.
  I opened Mathlib `LocalCohomology.lean`: its construction is an Ext colimit and
  its Cech characterization is explicitly future work. I opened the existing
  `AlternatingCechTotalComplex.lean`: its input is a finite family of scheme opens
  and a coefficient functor; it does not state this simultaneous ring/ideal theorem.

No mathematical or convention mismatch was found, so I left the Lean module and
node unchanged. The module defines no data, has one named theorem with `sorry`,
and has source/blueprint docstrings. Its proof docstring follows all six node
steps, including the actual Godement construction, natural Cech roof, augmentation
extension, and localization base-change calculation. Every line is at most 100
characters; all variables and universes are explicitly bound.

Independent validation: `scompile.py NZ lem-weil-pbc-ring-complex-functorial` on the
delivered module passed on the server in 3.0 seconds, nice 19, two threads, a
60-second per-file limit, without errors or warnings. Its required side-only
`RingedSiteModules` overlay also compiled (0.9 seconds). No local compiler or
library build was run.
