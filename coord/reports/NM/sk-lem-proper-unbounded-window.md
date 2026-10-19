## Worker report

Module: `Sheaf.Paper.ProperUnboundedWindow`. The main declarations are
`AlgebraicGeometry.ProEtale.properUnboundedWindow` and
`AlgebraicGeometry.ProEtale.properUnboundedWindow_padicAlgCl`. Both proofs are exactly
`sorry`. The real-data predicate `ProperUnboundedWindowAssertions` only expands the
conclusions of this node; it introduces no independent coefficient, category, or map.
No new nodes or dependency modules were needed.

Hypothesis and clause matching:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed algebraic closure is the existing
  `PadicAlgCl ℓ`; `(E : PadicAlgCl.FiniteIntermediateField ℓ)` ranges over all finite
  subextensions of that closure. This is the node's specified embedded finite E,
  without choosing a different scalar ring or requiring an extraneous extension.
- The standing setting inherited from the referenced heart bound is explicit:
  `(k : Type u) [Field k]`, `(p₀ : ℕ) [CharP k p₀]`, `hp₀ : 0 < p₀`,
  `hpℓ : p₀ ≠ ℓ`, scheme `Over` instances, `IsSeparated` and the two finite-type
  components `LocallyOfFiniteType` and `QuasiCompact` for both structure maps.
  `(p : X ⟶ Y) [p.IsOver (Spec (.of k))]` is a k-morphism.
- `[IsProper p]` is properness. `(d : ℤ)` is an arbitrary integer. `hd` is exactly
  the previously stated heart bound's geometric-fibre condition: each geometric
  fibre is the pullback along the algebraic closure of a residue field; every
  natural finite lower bound n on its topological Krull dimension must satisfy
  `(n : ℤ) ≤ d`. There is no added nonnegative-d assumption.
- In the finite-coefficient case Λ is `Profinite.continuousMapRingObj.{u} E`, the
  existing continuous-function condensed ring of that finite subfield. The other
  case uses `Profinite.padicAlgClRingObj.{u} ℓ`, whose sections take values in some
  finite subextension. It is not the ring of all continuous functions into Qbar.
- `condensedRingObj Λ X` and `condensedRingObj Λ Y` are the recorded pulled-back
  coefficients. `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ...`
  is their module-object category; `DerivedCategory` is its ordinary unbounded
  derived category. The site is unchanged; the abelian sheaves live in u+1.
- `DerivedCategory.homologyFunctor _ n` is the cohomology-sheaf functor of the
  dependency's Mathlib match. We use its ordinary ambient form, not Qbar pair-category
  cohomology. That dependency explicitly retains both forms in its record.
- `ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)` is IndCons:
  a small filtered colimit computed in the ambient module category, replete under
  isomorphism. The input premise quantifies this over every n in ℤ; this is Dic,
  without restricting to bounded or bounded-below complexes.
- `Rp_*` is `(CondensedRing.lowerStar Λ p).rightDerivedFunctor`. This is the
  total right derived functor of the whole module-object pushforward, exactly as
  used by the recorded `ProperHeartBound` dependency. It is not the derived functor
  of an underlying abelian-sheaf pushforward or a restriction to D-plus.
- The first conjunct gives IndCons membership of every target cohomology sheaf,
  hence preservation of Dic.
- The second conjunct says, for every integer b, `K.IsLE b` implies
  `(Rp_*K).IsLE (b + 2 * d + 1)`. The third says, for every integer a,
  `K.IsGE a` implies `(Rp_*K).IsGE a`. Mathlib `isLE_iff` and `isGE_iff`
  identify these with the node's precise cohomology-vanishing conditions.
- For every q in ℤ, the fourth conjunct gives IndCons membership of the last
  window cohomology sheaf and `IsIso` of both canonical arrows. The first arrow is
  `H^q.map (Rp_*.map ((t.truncLEι q).app K))`. The second is
  `H^q.map (Rp_*.map ((t.truncGEπ (q - 2*d - 1)).app ((t.truncLE q).obj K)))`.
  These have exactly the directions in `K ← A → B`, with A = τ≤q K and
  B = τ≥(q-2d-1) A. The required isomorphism is `(asIso alpha).symm ≪≫ asIso beta`.
  This is precisely the arrow-by-arrow meaning of the node's last proof step,
  not a bare existence of an unrelated endpoint isomorphism. The first conjunct
  puts H^q(Rp_*K) in IndCons; alpha makes the middle sheaf ind-constructible too.
  IndCons is full, so these maps and their inverses give the claimed isomorphism
  inside IndCons. No arbitrary comparison map has been supplied as a hypothesis.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` and its public imports:
  `Profinite.continuousCoefficientRingObj`, its commutative structure, and the
  already existing `Profinite.continuousMapRingObj`. For the concrete finite
  intermediate fields, the latter's Type-0 carrier is sufficient and is the exact
  ring used by `ProperHeartBound`; schemes still have arbitrary universe u. The
  generalized dependency does not require replacing that existing specialization.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`, and its
  commutative-ring-object instance. This dependency is closed upstream and needs
  no new lean binding.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and
  `isCommMonObj_condensedRingObj`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` (the recorded notion,
  not upstream arbitrary-matrix constructibility).
- `Sheaf.Paper.ProperHeartBound`: `ProperHeartBoundAssertions`, `properHeartBound`,
  `properHeartBound_padicAlgCl`. The fibre condition and full derived pushforward
  match those signatures.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, the exact recorded Mathlib match of
  def-weil-derived-cohomology-sheaves. The more specialized
  `Sheaf.Paper.PbcQbarStandardCohomology.pbcQbarCohomology` was read and is not the
  ambient category in this item.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its
  universal and uniqueness statements were read. This general dependency allows
  arbitrary quasi-isomorphic K-injective resolutions. Here the module category
  already has K-injective resolutions, and the existing published generic
  `Functor.rightDerivedFunctor` realizes that same total derived-functor notion;
  this is the framework's canonical choice used in the heart-bound declaration.
  No duplicate right-derived-functor construction or extra hypothesis is needed.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`, the recorded composite of
  mapMod and scalar restriction. Its total derived functor is exported by
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` was read: its record
  explicitly reuses Mathlib good truncations for this component of the composite
  node. We directly import `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`
  and use `DerivedCategory.TStructure.t.truncLE`, `truncLEι`, `truncGE`, `truncGEπ`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the setting dependency's `compactificationOverField` and its docstring were read.
  Its scheme hypotheses are rendered directly as the setting requires; no chosen
  compactification is required or added to the theorem.

The proof-only dependencies det-ambient-ind-derived-sums,
det-proper-unbounded-window-bounded-below, det-proper-unbounded-window-arbitrary,
and det-proper-unbounded-window-iso have no recorded declarations in this snapshot;
there are no available proof modules to import. Their complete roles are retained
in the theorem docstrings. The delivered theorem's statement does not depend on
these unstated theorem interfaces.

Edge cases checked before writing and on reread: K = 0; schemes empty, including
an empty fibre; negative d (not forcibly changed to a natural or d≥0); arbitrary
negative and positive a,b,q; no assumption a≤b; a cohomologically unbounded input;
all primes, with the inherited p₀≠ℓ restriction; finite extensions and condensed
Qbar separately. Empty fibres have bottom Krull dimension, so hd permits negative
d exactly as the heart-bound node does. A nonempty fibre tests n=0, forcing d≥0
only when it follows from geometry. IsZero is applied to module objects through
the t-structure predicates, never to a bare Type. No auto-bound variables, local
notations, local instances, hollow definitions, or proved theorems were added.

Searches made on 2026-10-18:

- msearch.py LeanFinder: “Proper pushforward of unbounded ind constructible pro
  etale l adic complexes has finite cohomological amplitude and is computed by a
  finite truncation window”. Eight hits, all generic DerivedCategory bounds and
  representing-complex results; no existing theorem for this statement.
- msearch.py Loogle: `DerivedCategory.IsLE, DerivedCategory.IsGE`. Two hits:
  `exists_iso_singleFunctor_obj_of_isGE_of_isLE` and
  `exists_iso_Q_obj_of_isGE_of_isLE`; neither is the proper pushforward theorem.
- msearch.py LeanSearch: “Proper derived pushforward of unbounded ind constructible
  l adic sheaves is computed by a finite cohomological window”. Eight generic
  sheaf-pushforward results; no matching pro-etale unbounded window theorem.
- msearch.py grep: `indConstructible|IndConstructible|proper.*window`: zero Mathlib hits.
- rg in upstream WeilConjectures and side lean/Sheaf for ind-constructibility,
  proper windows, and amplitudes: existing heart, extension, filtered-colimit,
  and triangulated-category results; no matching theorem. The side modules
  ProperHeartBound and AmbientIndDerivedTriangulated were opened in full.
- grep/rg upstream for `sk-lem-proper-unbounded-window`: no declaration.
- rg Mathlib, upstream WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for `properUnboundedWindow|ProperUnboundedWindowAssertions`: zero hits.

Validation: scompile.py NM sk-lem-proper-unbounded-window compiled the module
cleanly as both sandbox (13.0 seconds) and library (7.1 seconds). No warnings or
errors were printed. No direct Lean compiler, Lake build, or global build was run.

## Second reading by NM

This is the author's separate reread, not an independent-agent review; the task
explicitly forbids starting another agent and assigns independent review to the
maintainer. I reopened the node, source unit, referenced heart-bound setting and
final Lean file. I checked every binder and every conjunct against the mappings
above, including the order and direction of both truncation arrows, q-2*d-1,
b+2*d+1, no boundedness premise on the whole theorem, and full ambient derived
categories. The context omission was repaired explicitly as documented below.
No other mismatch was found. The only proofs are the two whole-theorem sorries.

## Statement corrected

The old expansion introduced arbitrary schemes while its source says p and d are
“as in sk-lem-proper-heart-bound”. That dependency explicitly carries the standing
positive-characteristic separated finite-type setting sk-def-sfb-dc-setting.
The corrected node spells out that inherited context and small-diagram convention.
This does not change the blueprint unit's own mathematical statement: it expands
its reference to the heart bound, rather than changing its coefficient categories,
conclusions, or proof route. The old unrestricted reading would not supply the
hypotheses for the recorded heart bound. Only statement, stmt_deps (adding the
already-landed sk-def-sfb-dc-setting), statement_change, and lean change; proof and
proof_deps are untouched.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-proper-unbounded-window/_section.md, opening reference to the heart bound;
sk-lem-proper-heart-bound and sk-def-sfb-dc-setting provide the inherited context.

Citer audit: rg -l for the quoted item id, followed by JSON filtering on stmt_deps
and proof_deps, found exactly these two actual citers (other files only mention
the id in blueprint/source/prose fields):

- det-proper-unbounded-window-ii-general: holds false as currently expanded.
  Its canonical-window naturality argument remains valid in the standing setting,
  but its unrestricted scheme binders omit that setting and require the same
  context clarification before this theorem applies.
- sk-lem-proper-unbounded-window-ii: holds false as currently expanded.
  Its preservation and canonical-window applications remain valid in the standing
  setting, but its unrestricted statement omits the needed base and finite-type
  hypotheses. Its use of the definition of Dic is unaffected. No citer is edited.

Old statement, verbatim:

Let $X,Y$ be schemes, $\ell$ a prime, $\Qlb$ an algebraic closure of $\mathbf Q_\ell$, and $E\subseteq\Qlb$ a finite extension of $\mathbf Q_\ell$. Let $\Lambda=E$ or $\Qlb$, understood as the condensed coefficient ring of [sk-def-sfb-condensed-ring] or [sk-def-sfb-qlbar-condensed], respectively. For $T=X,Y$, put $\Lambda_T=p_T^*\Lambda$ [sk-def-sfb-pulled-back-coefficients], and let $D(T_{\mathrm{proét}},\Lambda)=D(\Mod_{\Lambda_T})$ be the unbounded derived category of sheaves of $\Lambda_T$-modules, with cohomology sheaves $\mathcal H^n$ [def-weil-derived-cohomology-sheaves]. Write $\IndCons(T,\Lambda)$ for the full subcategory of sheaves isomorphic to filtered colimits, in $\Mod_{\Lambda_T}$, of constructible sheaves [sk-def-sfb-constructible], and define
$$
\Dic(T,\Lambda)=\{K\in D(T_{\mathrm{proét}},\Lambda):\mathcal H^n(K)\in\IndCons(T,\Lambda)\text{ for every }n\in\mathbf Z\}.
$$
Let $p:X\to Y$ be proper and let $d\in\mathbf Z$ bound the dimensions of all geometric fibres of $p$, as in [sk-lem-proper-heart-bound]. Let $Rp_*$ denote the total right derived functor [def-sfb-right-derived-functor] of the module pushforward [sk-def-sfb-module-pushforward-pullback]. For integers $a,b$, write $\Dic^{\leq b}(T,\Lambda)$ and $\Dic^{\geq a}(T,\Lambda)$ for the objects of $\Dic(T,\Lambda)$ whose cohomology vanishes in degrees $>b$, respectively $<a$. Use the canonical truncations of [def-kun-truncations]. Then $Rp_*$ maps $\Dic(X,\Lambda)$ into $\Dic(Y,\Lambda)$, and
$$
Rp_*\bigl(\Dic^{\leq b}(X,\Lambda)\bigr)\subset\Dic^{\leq b+2d+1}(Y,\Lambda),\qquad
Rp_*\bigl(\Dic^{\geq a}(X,\Lambda)\bigr)\subset\Dic^{\geq a}(Y,\Lambda).
$$
Moreover, for $K\in\Dic(X,\Lambda)$ and every $q\in\mathbf Z$, the canonical truncation maps
$K\leftarrow\tau_{\leq q}K\to\tau_{\geq q-2d-1}\tau_{\leq q}K$ induce an isomorphism in $\IndCons(Y,\Lambda)$
$$
\mathcal H^q(Rp_*K)\simeq\mathcal H^q\bigl(Rp_*\tau_{\geq q-2d-1}\tau_{\leq q}K\bigr).
$$
