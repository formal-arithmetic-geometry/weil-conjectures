## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFinitePresentationPushforwardConstructible`
states `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_finite_finitePresentation`
with a single `sorry`. It adds no definitions and changes only the item's `lean` record.

Hypothesis and conclusion correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`.
- Both schemes quasi-compact and quasi-separated: `[CompactSpace X]`,
  `[QuasiSeparatedSpace X]`, `[CompactSpace Y]`, `[QuasiSeparatedSpace Y]`.
- The given finite morphism: `(f : X ⟶ Y) [IsFinite f]`.
- Finite presentation, with exactly the node's convention:
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
  The latter two are consequences of finiteness, but are retained as the explicitly
  specified components of finite presentation, not additional mathematical restrictions.
- Finite commutative coefficient ring: `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`.
- A sheaf of Λ-modules on the small etale site:
  `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  This is the existing project's constant-ring module-sheaf encoding, with linear
  morphisms, not a replacement by sheaves of sets or abelian groups.
- Constructibility hypothesis: `(hF : IsConstructibleEtaleModuleSheaf F)`.
- Direct image and its constructibility: the conclusion is
  `IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)`.
  There is no derived image, higher cohomology, or extra conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category
  of morphisms, for `def-pc-scheme`.
- `def-weil-pbc-scheme-conventions` is a convention record with no declaration;
  its qcqs properties use `CompactSpace` and `QuasiSeparatedSpace`, and its finite
  presentation is the displayed three morphism properties.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  affine morphism with finite affine-open ring maps.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (the dependency's mathlib_match).
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`; this dependency provides
  the module-sheaf category context, not an extension-by-zero operation in this statement.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, the canonical site pushforward evaluating
  F on the base change of an etale test scheme; its coefficient category is arbitrary.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, read in full:
  a finite locally closed scheme stratification with constructible parts and finite
  constant module values after an etale cover of every stratum.

All recorded proof-dependency modules are imported without `public`, unless already
needed publicly by the signature. The convention-only dependency has no module.
Mathlib's finite-morphism permanence matches are supplied by Finite and Proper,
and closed immersions by the imported geometry modules. No import of a consumer is made.
The theorem docstring records the complete six-step proof route and named inputs.

Source checked: `literature/stacks-project/etale-cohomology.tex`,
`lemma-finite-pushforward-constructible` (Tag 095R), statement and proof. Its Noetherian
coefficient-ring assertion specializes to finite commutative rings as in this node.
The proof's phrase "surjective over X" is the known source typo: the node correctly
uses a surjection onto Y. No statement correction is needed here.

Edge cases checked: empty X and/or Y are allowed (no nonemptiness assumptions);
finite empty fibres give the zero direct-image module, which is constructible;
zero ring and zero sheaf are allowed; identity morphisms and finite non-etale
morphisms are included. No reducedness, flatness, etaleness, Noetherian scheme,
surjectivity, or nonzero-ring hypothesis is imposed. The one universe u follows
both the existing small-etale-site and constructibility APIs; finite coefficient
rings can be represented in Type (u + 1), and the sheaf modules have the same
universe as the recorded predicate. In particular no independent site-universe
equality or change of coefficient category is introduced.

Searches for reuse:

- `msearch.py leanfinder`, query "Finite finitely presented pushforward preserves
  constructible etale module sheaves": 8 hits, concerning quasi-coherent finite
  presentation and constructible images of spectral subsets; none states this result.
- `msearch.py loogle`, query `"constructible", "sheaf"`: 0 hits.
- `msearch.py grep`, query `constructible.*sheaf|sheaf.*constructible`: 0 Mathlib hits.
- `rg` in upstream WeilConjectures and project lean/Sheaf for
  `constructible.*[Pp]ushforward|[Pp]ushforward.*[Cc]onstructible|isConstructible.*lowerStar`
  found the existing finite-etale theorem (strictly stronger etaleness hypothesis),
  Noetherian finite-pushforward results (different scheme hypotheses), curve results
  (restricted schemes), and pro-etale adic finiteness (different coefficient category).
  None is this finite-presentation qcqs etale-module statement.
- The same source search included the exact item id, with no upstream declaration.
  The only project mention was a proof-route reference in QuasiFiniteShriekConstructible.

No disputed statement, new nodes, or dependency repairs.


## Second reading by NG

I independently opened the node, its seven statement-dependency records, the
recorded source declarations, the sandbox Lean file, and Stacks
`etale-cohomology.tex`, lines 12527–12549 (095R). The source states finite and
finitely presented, with a Noetherian coefficient ring, and assumes no further
scheme hypotheses in this lemma. The node explicitly takes its finite-ring,
qcqs specialization; finite commutative rings are Noetherian. No correction of
the node or audit of citers is needed.

Object/hypothesis/conclusion checklist, read before comparing the signature:

- Objects X and Y are schemes: `{X Y : Scheme.{u}}`. Verdict: exact; this is
  Mathlib's locally affine locally ringed space, not a restricted scheme category.
- X is quasi-compact and quasi-separated: `[CompactSpace X]`
  `[QuasiSeparatedSpace X]`. Verdict: exact scheme properties.
- Y is quasi-compact and quasi-separated: `[CompactSpace Y]`
  `[QuasiSeparatedSpace Y]`. Verdict: exact; no Noetherian-space assumption.
- A morphism f from X to Y: `(f : X ⟶ Y)`. Verdict: exact direction.
- f is finite: `[IsFinite f]`. I read Finite.lean:39–40: it extends
  `IsAffineHom f` and requires finite ring maps on every affine target open.
  Verdict: exactly the recorded finite-morphism node.
- f is finitely presented: `[LocallyOfFinitePresentation f] [QuasiCompact f]`
  `[QuasiSeparated f]`. FinitePresentation.lean:45–48 requires finitely presented
  maps on affine charts. Together these are exactly the convention node's three
  components. The latter two also follow from finiteness; they exclude no case.
- Lambda is a finite commutative ring: `{Λ : Type (u + 1)} [CommRing Λ]`
  `[Finite Λ]`. Verdict: exact, with no nonzero, field or characteristic condition.
- F is a Lambda-module sheaf on the small etale site of X:
  `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Verdict: exact
  existing coefficient encoding with linear morphisms. The extension-by-zero
  dependency is only the category context here, not an operation used in the claim.
- F is constructible: `(hF : IsConstructibleEtaleModuleSheaf F)`. I read the
  recorded definition in IsConstructibleEtaleModuleSheaf.lean in full and its
  LocallyClosedStratification structure: a finite partition, scheme immersions,
  constructible parts, and etale trivializations with finite constant modules.
  Verdict: the node's module notion, not merely constructible support or sets.
- The conclusion is constructibility of f_*F on Y, rendered by
  `IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F)`.
  I read UpperLowerStar/Defs.lean:159–165 and its ambient binders: lowerStar is
  precomposition with the etale base-change functor, valid for arbitrary f,
  objectwise F(W ×_Y X). Verdict: canonical ordinary module direct image, with
  no higher-image assertion or other conclusion. Quantifiers are in the intended
  order: schemes, map, coefficients, sheaf, constructibility, conclusion.

Edge cases: no nonempty scheme, nonzero ring or nonzero sheaf binder appears.
The empty scheme admits the zero-stratum partition (Fin 0), and empty finite
fibres give zero modules. Identity and finite non-etale morphisms are included.
There is no degree parameter n and no invertibility assumption on a characteristic.
The universe u is bound; the coefficient and module universe u+1 is exactly the
recorded constructibility and small-etale API convention. Any finite coefficient
ring has a representative there. The signature introduces no independent universe
identification or essential-smallness assumption. All variables are explicitly bound.

Independent reuse searches (2026-10-15):

- `msearch.py leanfinder`, query “A finite morphism of finite presentation carries
  constructible module sheaves to constructible sheaves by direct image”: eight
  hits, all constructible images of subsets or quasicoherent finite presentation,
  not this sheaf theorem.
- `msearch.py loogle`, query `"constructible", "lowerStar"`: zero hits.
- `rg` on Mathlib algebraic geometry, upstream ConstructibleSheaf and SixFunctors,
  and project lean/Sheaf/AlgebraicGeometry, using constructible with finite,
  pushforward and lowerStar, plus the exact declaration name and upstream name
  index. I opened FiniteEtalePushforwardConstructible (adds Etale),
  ConstructibleOfFiniteDirectImage (reverse implication with Noetherian schemes),
  and FinitePushforwardFiniteStalkModule (Noetherian target). None states this
  finite-presentation qcqs theorem; other curve and pro-etale hits have different
  objects or hypotheses. No duplicate declaration was found.

H5/H6/H8/H9: no definitions are added and the sole theorem has only `sorry` as
proof. Both docstrings name 095R and the exact blueprint id; the theorem docstring
covers all six node proof steps, including affine restriction, nonflat surjective
base change, module pullback, thickening equivalence, finite etale pushforward,
and descent. Imports include the recorded proof inputs. No private notation,
local instances, hidden statement lets, overlong lines or unbound names occur.
There are no new nodes or dependency modules to review.

Mismatches found: none. Changes: appended this independent second reading only;
the Lean file and node signature are retained verbatim. Compilation and delivery
checks are recorded below.

Validation: scompile.py compiled the delivered module cleanly (exit 0), with
no diagnostics. deliver2.py --no-push returned OK: preflight and compilation
passed. The node lean.statement was checked against the exact file signature.
