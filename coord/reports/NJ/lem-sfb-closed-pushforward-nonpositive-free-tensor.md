## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedPushforwardNonpositiveFreeTensor` states
`AlgebraicGeometry.isMPseudoCoherent_closedPushforward_tensor_nonpositive_free`.
Its only postponed proof is this theorem, with the complete eight-step node proof in
its docstring. There are no new definitions, dependency modules, or statement changes.
The node is copied unchanged except for its `lean` record.

Clause-by-clause correspondence:

- Affine schemes P and W: `(P W : Scheme.{u}) [IsAffine P] [IsAffine W]`.
- Closed immersion j: `(j : P ⟶ W) [IsClosedImmersion j]`.
- Integer m: `(m : ℤ)`, with no sign constraint.
- Arbitrary Q in D(O_P): `(Q : schemeDerivedCategory P)`. There is no quasi-coherence,
  upper-bound, lower-bound, or Tor-dimension hypothesis on Q.
- F is an actual cochain complex of O_P-modules:
  `(F : CochainComplex (SheafOfModules.{u} (moduleRings P.toRingedSpace)) ℤ)`.
- Positive terms vanish: `hF_zero : ∀ q : ℤ, 0 < q → IsZero (F.X q)`.
- Every nonpositive term is finite free: `hF_free : ∀ q : ℤ, q ≤ 0 → ∃ r : ℕ,
  Nonempty (F.X q ≅ SheafOfModules.free
  (R := moduleRings P.toRingedSpace) (ULift.{u} (Fin r)))`.
  Mathlib free is the coproduct of copies of the ring module; the lifted finite
  indexing type only matches the sheaf universe and does not restrict ranks.
- The assumed m-pseudo-coherence of Rj_*Q is exactly
  `hQ : Scheme.IsMPseudoCoherent W m ((schemeDerivedDirectImage j).obj Q)`.
- The conclusion uses the SAME degree-m predicate on
  `(schemeDerivedDirectImage j).obj (Q ⊗ DerivedCategory.Q.obj F)`.
  Thus F denotes its localized derived image, and tensor is the globally recorded
  K-flat derived tensor instance, not termwise underived tensor.
- F need not be bounded below: only positive degrees vanish, and ranks may be
  independently chosen in every nonpositive degree. No eventual negative vanishing
  or uniform rank bound is required.
- The HasDerivedCategory binders select the localization models used by the recorded
  interfaces. Source morphisms have universe wP, target morphisms wW; the target's
  open subschemes use wW as required by IsMPseudoCoherent. No equality between wP
  and wW is imposed.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its category of morphisms.
  Affineness is `AlgebraicGeometry.IsAffine` from `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, using the shared SheafOfModules carrier.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`, the K-injective derived direct image.
- `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent`; its full definition uses local strictly
  perfect approximations, cohomology isomorphisms above m, and epimorphisms at m.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `AlgebraicGeometry.schemeDerivedTensorMonoidal`, the global K-flat tensor instance.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`: `SheafOfModules.free` and its
  coproduct construction, used directly for finite freeness rather than defining it again.

All recorded proof-dependency modules are imported, privately when used only in the
postponed proof. They include truncations, flatness, perfectness, bounded-above flat
K-flatness, K-flat restriction, pushforward/restriction, total tensor/restriction,
localized exactness, closed-immersion projection formula, closed-pushforward stalks,
degreewise split triangles, exact-functor cohomology, and exact derived factorization.
`lem-sfb-ringed-site-m-pseudocoherent-triangle` currently has neither a Lean record nor
a Mathlib match; its future proof import is left for the maintainer when it is stated.
It is only a proof dependency and is not needed to type this theorem.

Source and edge cases:

Read `literature/stacks-project/more-morphisms.tex`, Tag 09US,
`lemma-pull-relative-pseudo-coherent`, including the entire tensor-filtration paragraph.
The extracted node explicitly repairs the printed tail inequality; the delivered proof
plan keeps the quotient zero in degrees >=m. The node's localization argument obtains
an upper bound on Q locally from an approximation of Rj_*Q and faithful exact closed
pushforward; it does not add the global upper-bound hypothesis in the surrounding
relative argument. No statement fault or STATEMENT-DISPUTED flag remains.

Checked: r=0 uses the empty coproduct and is allowed; degree q=0 is in the free clause,
not in the vanishing clause; q<0 is unrestricted in how far it extends. Zero Q, zero F,
empty schemes, the identity closed immersion, m=0, and negative m are included. A single
term in degree q<0 shifts Q by -q, so its cohomology is H^(i-q)(Q), in the required
approximation range i-q>=i. Separate wP/wW preserve the full derived-category size
choice. Empty-space local approximation is vacuous, as the source definition requires.

Searches (all via the prescribed msearch.py unless specified):

- leanfinder: "Tensoring by a nonpositive complex of finite free sheaves preserves m
  pseudo coherence after closed immersion derived pushforward". Eight hits, including
  LightCondensed monoidal structures, SheafOfModules.pushforward_assoc, and
  Scheme.Modules.pushforward; none states this fixed-degree assertion.
- loogle: `"PseudoCoherent", "tensor"`. Zero hits.
- leansearch: "Derived pushforward under a closed immersion preserves m pseudo coherence
  after tensoring with a nonpositive finite free complex". Eight hits concerning ordinary
  scheme module pushforward and IsClosedImmersion; none is this theorem.
- grep: `pseudo.?coher.*tensor|tensor.*pseudo.?coher` over Mathlib. Zero hits.
- rg in the read-only WeilConjectures and Sheaf trees: the same expression, together
  with nonpositive/tensor and the exact node id. Related all-degree pseudo-coherent
  tensor closure and tensor calculations occur, but no closed-pushforward degree-m
  theorem. In particular PseudoCoherentTensorClosure concerns ring-module complexes
  with different hypotheses and does not supply this statement.
- Exact declaration-name rg over Mathlib, WeilConjectures and Sheaf and exact node-id
  grep over WeilConjectures: no existing declaration or module match.

Validation: scompile.py compiled this delivery's module in both sandbox and library
contexts against the live server build, 7.0 s and 7.1 s, with no errors or warnings.
`set_option autoImplicit false` ensures all variables and universes are explicitly bound.

## Second reading by NJ

A second in-session reading of the node and completed file checked each binder against
the clauses above; this is not claimed to be an independent agent review. The dispatcher
requires this worker to deliver directly and the maintainer supplies independent review.
P and W are both affine; j is closed; degree zero is retained; finite ranks include zero;
no lower bound or quasi-coherence was inserted; F enters through DerivedCategory.Q;
tensor and derived direct image are the recorded canonical constructions; hypothesis
and conclusion use precisely IsMPseudoCoherent W m. No mathematical mismatch was found.
The proof docstring retains all eight steps and the corrected direction of tail vanishing.
