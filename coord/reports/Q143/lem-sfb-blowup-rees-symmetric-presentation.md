## Worker report

The module `Sheaf.AlgebraicGeometry.BlowupReesSymmetricPresentation` states
`AlgebraicGeometry.Scheme.IdealSheafData.blowup_rees_symmetric_presentation`, with
one `sorry` and no new definitions. The natural-language statement is unchanged.
The added statement dependencies are the already recorded
`def-trf-canonical-symmetric-graded-algebra` (the source of the symmetric graded
algebra interface) and `def-sbc-ideal-sheaf-powers` (the powers used in the affine
section identification). No dependency node is changed.

Hypotheses and clauses, in the order of the node:

- A scheme T is `{T : Scheme.{u}}`. The arbitrary universe u is explicit.
- A quasi-coherent ideal is `I : T.IdealSheafData`, the recorded affine-local
  ideal-sheaf notion. Its actual module is the existing `I.toModules`. Because
  the affine-local ideal datum already describes a quasi-coherent ideal, the
  statement produces `hqc : I.toModules.IsQuasicoherent` rather than imposing
  another assumption on I. This witness only supplies the class argument of
  the existing symmetric graded-algebra construction. There is no finite-type,
  Noetherian, nonzero-ideal, separatedness or affineness hypothesis.
- The ordinary glued blowup B and its map b are the existing `I.blowup` and
  `I.blowupMap`, defined using `blowupGluingData`. No alternate model is introduced.
- The sheaf Rees algebra R is the recorded `I.reesData`. Its sections over an
  affine U are definitionally `reesAlgebra (I.ideal U)`, its grading is
  `reesGrading`, and its restrictions are coefficientwise `reesGrading.hom`.
  Its degree-zero algebra is canonically the base ring by `reesGradingZero` and
  `algebraMap_reesGrading_zero` in the imported source. The existing
  `powMulMap` and `reesMonomial_mul_reesMonomial` give its ideal-power products.
- Sym(I) with symmetric degree is the existing
  `@SymmetricAlgebraSheaf.gradedAlgebraData T I.toModules hqc`. Its affine ring
  is literally the symmetric algebra of the module sections, its nth grade is
  the nth power of the image of the degree-one inclusion, and its restrictions
  are the universal symmetric extensions. This is the same grading as the
  recorded `SymmetricAlgebra.graded_by_tensor_images` theorem.
- The existential `q` is a `GradedAlgebraData.Hom` between these two specific
  algebras. Its `app` is a graded ring homomorphism; `app_algebraMap` says it
  fixes scalars, hence is the identity in degree zero under the two canonical
  degree-zero identifications; `naturality` supplies compatibility with every
  affine restriction. As specified in the recorded relative-Proj dependency,
  this is the affine-basis presentation of a morphism of quasi-coherent graded
  algebra sheaves, not an unrelated family of local maps.
- `∀ U, Function.Surjective (q.app U)` gives affine surjectivity and therefore
  surjectivity of the corresponding sheaf morphism: affine opens form a basis.
- For every n, including n=0, the displayed finite-product equation sends the
  symmetric product of n ideal sections to the polynomial monomial with their
  product as coefficient. The inputs range over actual `Γ(I.toModules,U)`;
  `I.toModulesι.app` is their inclusion in the base ring. Thus these are exactly
  the x_i in the node. For n=1 this prescribes the canonical degree-one inclusion;
  the universal property makes q canonical. No arbitrary map is assumed.
- The bijectivity of the actual symmetric sheaf's canonical `sectionMap` gives
  Γ(U,Sym(I)) = Sym_{O(U)}(Γ(U,I)), with its unit and generators fixed, as
  required. The ring homomorphism is an existing definition and the theorem
  asserts its bijectivity, not an arbitrary isomorphism.
- The range equality for `(I^n).toModulesι.app U` identifies Γ(U,I^n) with
  `(I.ideal U)^n` inside O(U). The imported `injective_toModulesι_app` gives
  injectivity of this very map; thus this is an identification of modules, not
  merely a statement about a noninjective image. The case n=1 identifies Γ(U,I)
  with the ideal used everywhere else.
- `DirectSum.decomposeAlgEquiv (reesGrading (I.ideal U))` is already an algebra
  equivalence from the affine Rees ring to the direct sum of its homogeneous
  pieces. The existing `reesGradingEquivPow (I.ideal U) n` identifies the nth
  piece with `(I.ideal U)^n`. The asserted equation states that the resulting
  nth entry is the nth polynomial coefficient. Together these are precisely
  the canonical graded identification with the direct sum of ideal powers:
  the inverse sums the monomials. Products on pieces are ordinary multiplication
  of coefficients by `reesMonomial_mul`, so this identification preserves
  convolution multiplication, not just the underlying module.
- The canonical e is the existing isomorphism `I.relProjReesIso.symm` of type
  `I.blowup ≅ I.reesData.relProj`. The equality involving `relProjReesIso.inv`
  and `relProjHom` asserts that it lies over T. Using the existing isomorphism
  also fixes its canonicity; no construction is chosen from mere existence.
- For every affine U, `I.blowupι U ≫ I.relProjReesIso.inv = I.reesData.relProjι U`
  asserts that e restricts to the identity between the two identical local
  Proj models. These embeddings identify the local schemes with the inverse
  images of U, by the recorded `isPullback_blowupι` and `isPullback_relProjι`.
- The next equality states compatibility with both transition functors on
  every inclusion of affine opens. The last polynomial equation explicitly
  identifies Rees restriction with coefficientwise application of structure
  sheaf restriction. On a principal open this is exactly coefficientwise
  localization a*t^n mapping to (a/1)*t^n. Thus the transition equation retains
  the specified localization maps, including nontrivial refinements.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, and its public Mathlib imports:
  `SheafOfModules.IsQuasicoherent`. Only the quasi-coherent notion in the
  three-part node pqf-def-coherent is used; its finite-type predicate is not
  imposed on this item.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`,
  `blowupFunctor`, `blowupι`, `blowupGluingData`, `isPullback_blowupι`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Rees`: `reesData`, `powMulMap`,
  `reesMonomial_mul_reesMonomial`, `relProjReesIso`, and its over-base/chart lemmas.
  The Rees node has no lean record, but its closed upstream audit explicitly
  records reesData; this is the required upstream declaration.
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images` (via the canonical graded interface).
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `exists_quasiCoherentSymmetricAlgebra`; its actual constructed algebra and
  section map come from `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`.
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `SymmetricAlgebraSheaf.gradedAlgebraData`, with `gradedRestriction` and the
  explicit affine rings and symmetric grades.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `IdealSheafData.ideal_pow`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `toModules`,
  `toModulesι`, `range_toModulesι_app`, `injective_toModulesι_app`.
- `WeilConjectures.Blowup.Affine.ReesPieceLocalization`: `reesGradingEquivPow`;
  `Mathlib.RingTheory.GradedAlgebra.Basic`: `DirectSum.decomposeAlgEquiv`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` and `GradedAlgebraData`:
  `relProj`, `relProjHom`, `relProjι`, `relProjFunctor`, `GradedAlgebraData.Hom`.
- Plain proof imports retain the stated relative-Proj affine restriction and
  scheme gluing inputs. The proof node `lem-sfb-sheaf-rees-symmetric-presentation`
  has no recorded declaration and so has no module to import. It is a proof
  dependency only; no missing statement notion or assumed theorem is substituted.
  The theorem docstring reproduces all four proof steps, including the overlap
  and cover-independence checks.

Edge cases checked before writing: the zero ideal has no positive Rees pieces
and empty Proj; the unit ideal gives O[t] and blowup T; the zero ring and empty
scheme are allowed. For n=0 the empty product gives the unit monomial, and for
n=1 it gives precisely the ideal inclusion. Infinite generation is allowed:
individual symmetric and polynomial expressions still have finite support.
The affine opens need not have affine pairwise intersections, since the
construction and equations use all affine refinements. No universe equality
or size restriction beyond `Scheme.{u}` and its existing module category is used.

Searches made before writing:

- msearch LeanFinder, query: "The symmetric algebra of a quasi coherent ideal
  surjects onto its graded Rees algebra and the blowup is its relative Proj".
  Eight hits, chiefly Proj.fromOfGlobalSections, Proj, away charts and unrelated
  surjectivity lemmas; no complete match.
- msearch Loogle, query `SymmetricAlgebra, reesAlgebra`: zero hits.
- msearch grep, query `reesAlgebra|ReesAlgebra|relProjReesIso`: ten hits, mostly
  Mathlib RingTheory/ReesAlgebra and Filtration; ring definitions only.
- msearch LeanSearch, query: "The blowup of a scheme along a quasi coherent
  ideal is relative Proj of the Rees algebra with a graded surjection from the
  symmetric algebra": eight hits, including reesAlgebra, Proj and generic
  Proj construction lemmas; no complete match.
- rg in the specified WeilConjectures and Sheaf directories for symmetric/Rees
  combinations and the item id found the existing relative-Proj comparison,
  the canonical symmetric interface, and downstream consumers, but no combined
  statement. The final declaration name and exact item id had no match in those
  roots or dag/lean_names_upstream.json.
- The canonical symmetric module was additionally read using `scompile.py --source`;
  its server version agrees with the local source.

Source checked directly: literature/stacks-project/divisors.tex,
lemma-blowing-up-projective (Tag 02NS), its displayed graded quotient and
relative-Proj identity; lemma-blowing-up-affine (Tag 0804). The finite-type
assumption of the projectivity conclusion in 02NS is not needed for the
quotient or the Proj identity stated here, as confirmed by 0804.

No STATEMENT-DISPUTED issue or statement correction. No new nodes or dependency
modules. Compiler repair changed only notation/coercion syntax: explicit
structure-ring types disambiguate module-section notation; `@id` exposes the
existing definitional identification of unit-module sections with ring sections;
the actual Rees subtype map coerces its affine-basis presentation to polynomials.

## Second reading by Q143

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
