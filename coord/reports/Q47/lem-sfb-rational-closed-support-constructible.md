## Worker report

The module `Sheaf.Paper.RationalClosedSupportConstructible` states
`AlgebraicGeometry.ProEtale.CondensedRing.rationalClosedSupportConstructible`.
Its only postponed proof is this named theorem, with the six DAG proof steps in its docstring.
No definitions, new nodes, dependency repairs or statement corrections are introduced.
The node changes only in `lean`.

Hypothesis and clause correspondence:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A field k of characteristic p > 0 different from ell:
  `(k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)`.
  Primality of the positive field characteristic follows from the source assumptions;
  conversely the prime binder ensures positivity.
- X and Z are separated and finite type over k: their `Over (Spec (.of k))`
  instances, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` structural-map
  instances. These are precisely finite type and separatedness, with no smoothness,
  reducedness, connectedness or dimension assumptions.
- The given closed immersion is `(i : Z ⟶ X) [IsClosedImmersion i]`;
  `[i.IsOver (Spec (.of k))]` makes it a k-morphism.
- The defining open complement for the existing support functor is exposed as
  `(j : U ⟶ X) [IsOpenImmersion j]` and
  `hij : Set.range i.base = (Set.range j.base)ᶜ`.
  This is presentation data for the functor in the node, not a restriction on i.
  The canonical complement always supplies it. U inherits its k-structure through j;
  it is again separated and finite type since X is Noetherian. No additional
  quasi-compactness assumption on j is imposed.
- A finite subextension in the fixed algebraic closure is
  `E : PadicAlgCl.FiniteIntermediateField ℓ`: by the actual definition this is an
  intermediate field of `PadicAlgCl ℓ / ℚ_[ℓ]` with `FiniteDimensional ℚ_[ℓ] E`.
  This is a concrete representative for the fixed closure, not its completion.
- The first conjunct uses `Profinite.continuousMapRingObj.{u} E`, exactly the
  continuous-function condensed ring with the subspace field topology.
- The second conjunct uses `Profinite.padicAlgClRingObj.{u} ℓ`, whose sections are
  continuous functions valued in a single finite subextension, not the full
  continuous-function ring into the algebraic closure.
- The pulled-back coefficients are the existing `condensedRingObj Λ X` and
  `condensedRingObj Λ Z`, inside `FormalSupportModules`.
- For either coefficient choice, K is in the actual ambient `DerivedCategory`
  of these module objects. The premise `constantModelBoundedConstructible Λ X K`
  is boundedness plus every integer cohomology sheaf being constructible in the
  finite constant local model convention of the recorded dependency. On the
  Noetherian schemes here its qcqs finite-stratification branch applies.
- The conclusion is exactly `constantModelBoundedConstructible Λ Z`
  applied to `((formalClosedSupport Λ i j).rightDerivedFunctor.obj K)`.
  This is the existing right derived functor of i* ker(id -> j*j*), not an arbitrary
  adjoint or a replacement construction. Universal quantification over E and the
  conjunction with the algebraic-closure case expresses the two choices of Lambda.
  No finite Tor-amplitude premise or conclusion is present.

Statement dependencies read and used:

- `sk-def-sfb-dc-setting`: the explicit scheme/base binders follow the existing
  `compactificationOverField` convention in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  No compactification datum is needed by this closed-support assertion.
- `sk-def-sfb-condensed-ring`: `Profinite.CondensedRing` in
  `Sheaf.Topology.ProfiniteCondensedRing` reexports the existing continuous coefficient
  constructors; `Profinite.continuousMapRingObj` supplies the E coefficient.
- `sk-def-sfb-qlbar-condensed`: its closed slopmaster2 audit, despite having no `lean`
  record, names `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`
  in `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. Read their full
  definitions and subfunctor/sheaf construction from the shared upstream overlay.
- `sk-def-sfb-pulled-back-coefficients`: `coefficientRing` and `condensedRingObj`
  in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`; the latter is
  `(upperStarFromPoint X).obj Λ` with the transported ring-object structure.
- `sk-def-sfb-constructible`: `IsConstantModelConstructible` and
  `constantModelBoundedConstructible` in `Sheaf.Paper.CondensedConstantConstructibility`.
  Read its finite constant local model, finite strata and affine-local fallback.
- `def-weil-closed-immersion`: Mathlib's `AlgebraicGeometry.IsClosedImmersion`
  (closed embedding and surjectivity on stalks), from `Morphisms.ClosedImmersion`.
- `sk-lem-formal-closed-support`: `formalClosedSupportAssertions` in
  `Sheaf.Paper.FormalClosedSupport`, exporting the actual `formalClosedSupport`
  kernel/pullback functor from `Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction`.

The public imports expose these interfaces. The plain proof imports include all
recorded proof-dependency modules, also Mathlib's Noetherian and quasi-separated
permanence interfaces and the source stratification pullback. Two proof dependencies
have no declaration yet: `det-lem-formal-closed-support-derived` and
`lem-sfb-rational-open-direct-image-constructible`; their proof steps remain explicit
in the docstring. They introduce no notion needed to type this statement. The
existing formal-support module already supplies the support functor.

Edge cases checked before writing and on rereading: K = 0; Z empty (support is zero);
i the identity (empty open complement, support is the identity); X empty; nonreduced
closed subschemes (no reducedness premise); E = ℚ_ell; arbitrary finite extensions;
zero or negative cohomological degrees (boundedness uses the entire integer-indexed
cohomology). The universe u remains arbitrary; the scheme site and Ab.{u+1}
convention are the existing small pro-etale framework, without an imposed universe
identification. The p = ell and characteristic-zero cases are excluded exactly as
in the node. No counterexample or statement dispute was found.

Source read: current main-20261015 blueprint's
`sk-prop-closed-adjoint-constructible-support.md` and its proof, both paragraphs.
The theorem only states its final constructibility conclusion, as this DAG item
requires; it does not add the surrounding unit's triangle or pushforward conclusions.

Searches (the wrapper recorded its own results in searches.jsonl):

- msearch leanfinder: "Derived closed support preserves bounded constructible rational
  l-adic sheaves with finite constant local models". Eight unrelated support and
  derived t-structure hits; no exact statement.
- msearch loogle: "DerivedCategory, IsClosedImmersion". Unknown identifier
  IsClosedImmersion, so inconclusive; retried with string query
  `"DerivedCategory", "support"`, successful zero hits.
- msearch leansearch: "Sections with closed support preserve bounded constructible
  complexes for rational l-adic condensed coefficients". Eight unrelated support,
  condensed colimit and module-ideal hits; no exact statement.
- msearch grep: `formalClosedSupport|constantModelBoundedConstructible` in Mathlib's
  AlgebraicGeometry: zero hits.
- rg on upstream WeilConjectures for the item id: zero hits. Searches for
  `constantModelBoundedConstructible` and rational closed-support names: no match
  in the older checkout. Shared upstream overlay search found
  `ProEtale/Derived/LocalizationConstructible.lean`; read its support theorem,
  which is for finite discrete rings killed by an integer invertible in k, with
  `Sheaf ... (ModuleCat Λ)`, not rational condensed module objects, hence not a match.
- rg on shared `lean/Sheaf` found the recorded finite-model definition and formal
  support construction, and the field-coefficient triangulated-closure theorem,
  but no preservation theorem for their combination. Full-name collision searches
  in Mathlib, both upstream source trees, Sheaf and dag/lean_names_upstream.json
  found no `rationalClosedSupportConstructible` declaration.

Validation: the first prescribed scompile run elaborated both sandbox and library
forms successfully in 5.1 seconds each, and identified a single long-line warning.
That line was split. The final prescribed scompile run passed with no warnings or errors
(sandbox 9.2 s, library 6.6 s). The prescribed deliver2 --no-push dry run then
reported OK: preflight and per-file compilation passed, with only the module,
node record and worker report staged. No other warning or error was reported.

## Second reading by Q47

Reread the node, current blueprint source, dependency definitions and complete module
with the hypothesis/clause correspondence above. This is a worker self-reread: the
brief explicitly forbids starting another agent; the maintainer provides independent
review on delivery. The two coefficient clauses exactly preserve the coefficient
constructors, finite-model constructibility predicate, ambient module category,
closed-support functor and all field/scheme assumptions. The auxiliary complement
j is always available and introduces no extra geometric restriction. Finite type
is rendered by both locally finite type and quasi-compactness, and all k-morphism
structure of the given i is retained. No mathematical mismatch was found. The only
edit resulting from compilation/rereading was splitting the 104-character final
conclusion line. No source statement or DAG dependency was changed.
