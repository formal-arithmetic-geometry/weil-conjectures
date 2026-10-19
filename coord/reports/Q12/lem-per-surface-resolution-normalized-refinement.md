## Worker report

The module states `AlgebraicGeometry.exists_regular_normalized_point_blowup_tower`
with a single `sorry` proof. Source: Stacks Project, resolve.tex, Tag 0BGM
(`lemma-existence-implies-existence-by-normalized-blowing-ups`), together with the
normalized-point-blowup definition, Tag 0BBS. Both source passages were read in full.
The theorem docstring reproduces all ten DAG proof steps and their dependencies.
No definitions, additional nodes, dependency repairs, or statement corrections are needed.

Hypotheses, matched individually:

- The commutative ring A is `(A : Type u) [CommRing A]`.
- Noetherian: `[IsNoetherianRing A]`.
- Local: `[IsLocalRing A]`; its unique closed point is `IsLocalRing.closedPoint A`.
- Normal local domain: `[IsDomain A] [IsIntegrallyClosed A]`, the recorded domain
  specialization of def-weil-pbc-normal-ring, with no extra excellence/Nagata assumption.
- Krull dimension two: `hDim : ringKrullDim A = 2`.
- The given integral scheme: `(T : Scheme.{u}) [IsIntegral T]`.
- Regularity of T: `hT : IsRegularScheme T`, which includes local Noetherianity.
- The given proper map to the spectrum: `(f : T ⟶ Spec (CommRingCat.of A)) [IsProper f]`.
- The induced function-field isomorphism is `hη` identifying the generic points and
  `hBir : IsIso (f.functionFieldMap hη)`. This is the canonical generic-stalk map
  induced by f, rather than an arbitrary isomorphism between abstract fields.
  Binding a given T and f universally states the implication from the assumed
  existence of such a model without requiring any extra model property.

Conclusion, matched clause by clause:

- Finitely many levels are `n : ℕ` and `X : Fin (n + 1) → Scheme.{u}`.
- Their structure maps are `p : ∀ i, X i ⟶ Spec (CommRingCat.of A)`.
- `IsIso (p 0)` identifies the initial scheme with Spec A over Spec A. This is the
  categorical presentation of X_0 = Spec A: using that isomorphism, replace the
  initial level by Spec A and compose the first arrow with p 0. Conversely, a
  literal tower starting at Spec A has p 0 equal to its identity. Neither direction
  changes the centers, properness, finiteness, or endpoint regularity.
- `∀ i, IsIntegral (X i)` gives integrality at every level, including both endpoints.
- `∀ x, IsDomain ((X i).presheaf.stalk x) ∧ IsIntegrallyClosed ...` gives normality
  at every point of every level, using the recorded normal-domain notion.
- `IsRegularScheme (X (Fin.last n))` gives the regular endpoint.
- For each `j : Fin n`, the predecessor is `X j.castSucc` and successor is `X j.succ`.
  The existential x is closed by `hx : IsClosed ({x} : Set (X j.castSucc))`.
- The point ideal is constrained by `I = Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩`.
  Mathlib's docstring explicitly identifies its quotient with the reduced induced
  closed subscheme. Thus the center has exactly the specified reduced structure.
- `p j.castSucc x = IsLocalRing.closedPoint A` places every center above the closed
  point of Spec A, with respect to the compatible structure maps of the whole tower.
- The integral witness for `I.blowup` makes the function-field normalization available.
  This is a conclusion witness, not a new assumption on A or the input model. The
  ordinary blowup of an integral surface at a closed point is integral, as explained
  in proof Step 9. The witness supplies the existing normalization's typeclass only.
- `e : X j.succ ≅ I.blowup.normalization` identifies the next level with the actual
  normalization of that ordinary blowup in its own function field.
- `IsFinite I.blowup.fromNormalization` is exactly finiteness of every normalization.
- `IsProper (e.hom ≫ I.blowup.fromNormalization ≫ I.blowupMap)` is properness of each
  normalized blowup arrow. The arrow is the canonical normalization map followed by
  the existing blowup map, after the presentation isomorphism e.
- The last equation identifies that arrow followed by the preceding structure map
  with `p j.succ`. It makes all maps to Spec A the composites of the tower arrows.
- There is no positivity restriction on n; `Fin 0` has no centers or arrows. The
  single level is then simultaneously the initial level and regular endpoint.

Dependency interfaces read and used:

- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs, `IsNoetherianRing`.
- def-weil-pbc-normal-ring: Mathlib.RingTheory.IntegralClosure.IntegrallyClosed,
  `IsIntegrallyClosed`, with `IsDomain` as its recorded normal-domain specialization.
- def-weil-pbc-krull-dimension-ring: Mathlib.RingTheory.KrullDimension.Basic, `ringKrullDim`.
- def-weil-regular-scheme: Sheaf.AlgebraicGeometry.IsRegularScheme, `IsRegularScheme`.
- def-pc-integral-scheme: Mathlib.AlgebraicGeometry.Properties, `IsIntegral`.
- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper, `IsProper`.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, `Spec`.
- def-sc-function-field: Sheaf.AlgebraicGeometry.FunctionField imports Mathlib's
  `Scheme.functionField`, which is the node's arbitrary-integral-scheme clause;
  `Scheme.Hom.functionFieldMap` comes from the published upstream
  WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback. Its full source was read
  with `scompile.py --source` because it is missing from the older source checkout.
- def-nagata-global-blowup: WeilConjectures.Blowup.Gluing,
  `Scheme.IdealSheafData.blowup` and `blowupMap`.
- def-sc-normalization: WeilConjectures.Mathlib.AlgebraicGeometry.Normalization,
  `Scheme.normalization` and `Scheme.fromNormalization`.
- def-weil-finite-integral-morphism: Mathlib.AlgebraicGeometry.Morphisms.Finite, `IsFinite`.
- The auxiliary point-ideal construction is the existing
  Mathlib.AlgebraicGeometry.IdealSheaf.Basic, `Scheme.IdealSheafData.vanishingIdeal`.
  No new notion or private replacement is introduced.

Recorded proof dependencies with available modules are imported without `public`,
unless their module is already public for the signature. The following proof nodes
have neither a recorded Lean declaration nor a Mathlib match and therefore have no
module to import: lem-per-excellent-normal-surface-local-data,
lem-per-excellent-normalized-blowup-tower, lem-per-excellent-surface-normalized-domination,
lem-per-local-normalized-blowups-globalize, lem-per-normalized-blowup-completion-descent,
lem-per-rational-surface-point-blowup-resolution, lem-per-regular-model-completion,
lem-per-regular-surface-birational-rational-local-rings. They are proof prerequisites,
not missing notions required to type this statement. Their proof steps remain in
its docstring and the DAG is unchanged.

Edge cases checked before writing:

- n = 0 retains the identity resolution when Spec A is already regular. No last-arrow
  indexing or nonempty-center assumption excludes this case.
- The empty scheme T is excluded by the source's integral hypothesis, represented by
  IsIntegral; no unnecessary nonemptiness hypothesis is added to the tower.
- Zero rings, fields, and dimension-one rings do not meet the input domain/dimension-two
  hypotheses. No characteristic restriction occurs, so positive and zero characteristic
  are both included.
- The normalization of an ordinary blowup is formed only after the existential integral
  witness, avoiding an implicit assumption that all ordinary blowups are already normal.
- All rings and schemes use the common arbitrary universe u, so generic stalks and the
  blowup/normalization constructions stay in the same geometric universe.

Searches for reuse:

- msearch.py LeanFinder: "A resolution of a normal two dimensional local scheme can be
  replaced by finitely many normalized point blowups"; eight hits, all relative
  normalization constructors and maps, no surface-resolution refinement theorem.
- msearch.py Loogle: `"normalization", "blowup"`; zero hits.
- msearch.py grep: `normalized.*blow|blow.*normali` in AlgebraicGeometry; zero hits.
- msearch.py LeanSearch: "A normal Noetherian local surface with a regular proper
  birational model has a resolution by normalized blowups at points"; eight relative
  normalization/interface hits, no matching theorem.
- rg of `normalized.*blow|blow.*normali|surface_resolution_normalized` and the exact
  item id in /home/ubuntu/weil-src-slopmaster2/WeilConjectures and lean/Sheaf, plus
  rg of dag/lean_names_upstream.json: no matching theorem. Side hits include
  NormalizedBlowupCalculus (componentwise normalization), MonoschemeToricRealization
  (arbitrary ideal-center towers), and ExcellentSurfaceDesingularization (a different
  excellent-global-surface theorem). None states the local nonexcellent result here.
  Existing blowup, point-ideal and function-field normalization definitions were reused.

Validation: scompile.py compiled the delivered module both as sandbox and its final
library module, cleanly (2.5 s and 2.6 s respectively). Every variable and universe
is explicitly bound; `autoImplicit` is false. No disputed statement or node fault found.

## Second reading by Q12

Author self-check, not an independent review; the maintainer performs independent review.
Reopened the node and the completed module and checked every hypothesis and conclusion
against the correspondences above. In particular, hBir is induced by the given f;
regularity uses the recorded locally-Noetherian predicate; every point ideal is exactly
the vanishing ideal of the closed singleton; the displayed normalization is in the
blowup's function field; finiteness and properness refer to the correct separate maps;
and the structure equations fix the support condition relative to the original base.
The base isomorphism is equivalent to the literal initial Spec A by the replacement
explained above. Fin n indexing leaves the zero-length case intact. There was no
statement mismatch requiring a correction or dependency module. No proof was attempted.
