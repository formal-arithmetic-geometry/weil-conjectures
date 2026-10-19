## Worker report

The module Sheaf.Paper.CompactificationProjectionPasting states the conditional formal
pasting identity of lem-sf-pf-compactification-pasting. Its only postponed proof is
CategoryTheory.SuppliedExchangeProjection.CompactificationPastingData.compactification_pasting.
The docstring contains all seven proof steps, retaining the two factor identities as
hypotheses. All auxiliary definitions contain real functor and morphism data.

The statement uses the supplied-domain interface of def-exchange-projection, rather than
assuming extra closure or base-change results. CompactificationPastingData extends the
recorded ExchangeProjectionStage. This is notation for the operations and comparisons
already supplied in the node, rather than a replacement definition of six operations.
Like the dependency's supplied-domain interface, it can be instantiated at any coefficient
stage, including on the finite ambient category when a tensor is unbounded. The node's
six-functor and geometric setting supplies those operations; the formal calculation uses
only their displayed natural transformations, not axioms asserting their invertibility.
The finite-field datum and scheme compactification introduce no additional arrow into
this conditional calculation. The auxiliary record collects the complete displayed
algebraic diagram; it makes no existence assertion about its realization.

Clause-by-clause correspondence:

- The categories DX, DB, DY, DX', DB', DY' denote the supplied coefficient domains on
  X, the compactification, Y, and their pullbacks. Each has independent object and Hom
  universes. The inherited properPull, properPull', horizontal,
  compactifyingHorizontal, horizontal', openPull, openPull' are F,F',G,H,A,J,J'.
  properPush and properPush' are R,R', and openExtension/openExtension' are j_!,j'_!.
- The inherited properPullbackComparison is theta: G followed by F' is isomorphic to
  F followed by H. openSquare is sigma: J followed by A is isomorphic to H followed by J'.
  openBaseChange is precisely beta, with its dependency orientation.
- properExchange is the mateEquiv construction for the recorded proper adjunctions,
  not a free exchange map. properProjection and properProjection' are exactly
  Adjunction.rightAdjointProjectionMap of the recorded tensor comparisons and counits.
- tensorHorizontal, tensorCompactifying and tensorOpenHorizontal are mu_G, mu_H, mu_A.
  These are natural isomorphisms of bifunctors, so their full two-variable naturality is
  retained. openTensor/openTensor' are the displayed gamma_j/gamma_j' at arbitrary ambient
  tensor inputs, before identifying JF with the composite pullback. The final field
  openProjectionNormalization ties this coordinate convention to the dependency's
  openProjection via the supplied pullFactorization. No second projection map is assumed.
- K and L range over the supplied domains. On the node's concrete realization these are
  K in D^b_c and L in D^b_ctf; no finite-Tor hypothesis is imposed on K. M and Q are expanded
  as openExtension.obj K and tensorBar applied to M and F.obj L. The formal lemma applies
  to every defined pair, so in particular the node's specified domains.
- tensorTarget is exactly d: mu_H followed by tensoring theta inverse in the second
  factor. openTarget is exactly z_K: beta at K tensor JFL, then j'_! of mu_A followed by
  tensoring sigma at FL. targetComparison is v: z_K followed by j'_! of J'(theta inverse)
  in the second tensor factor. Every source and target is given explicitly.
- FactorIdentities.openFactor is the first displayed hypothesis, with Lean's left-to-right
  composition. FactorIdentities.properFactor is the second displayed hypothesis at exactly
  M and Q above; it uses tensorTarget, not an arbitrary comparison.
- projection is exactly PF^c=R(gamma_j) pi_p in bare JF coordinates. leftPath is the
  three factors G(PF^c), e_T, R'(v). rightPath is the four factors mu_G,
  (e_M followed by R'(beta_K)) tensor identity, pi', and R'(gamma_j'). Its endpoints
  are definitionally identical to those of leftPath. The theorem's first conjunct equates
  their ComposableArrows.hom, which is their ordered composite.
- The second conjunct expresses naturality under maps intertwining all the component
  arrows, using morphisms of the actual ComposableArrows paths after any functor V.
  The two source components and two target components agree by hs and ht. The cross
  equalities transport the proved equality through these commuting component squares.
  D' may change all operation/comparison data of the same diagram type; it is not
  assumed to satisfy the factor identities. This is conditional naturality, with no
  claim to produce additional comparison maps.
- The final conjunct gives conjugation of the actual two paths by arbitrary supplied
  endpoint isomorphisms, after any functor V. source.hom has the node's u inverse
  orientation, target.hom its w orientation. In applications V is identity for a
  compactification change, or a supplied coefficient comparison functor. No inverse
  of e or pi occurs, and no detection of integral equalities by reductions is asserted.

Dependency declarations read and used:

- Sheaf.Paper.ExchangeProjectionSuppliedDomains:
  CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage and the
  compactificationProjectionFromData formula, with their full docstrings and signatures.
  The construction uses the same mateEquiv and rightAdjointProjectionMap as that module.
- Sheaf.Paper.SixFunctorDatum: WeilConjectures.SixFunctorDatum; read its full A1--A6
  record, its operation datum and the SixFunctorExchangeData normalizations. This is
  imported as a proof/context dependency; no A2 or A3 invertibility axiom is invoked.
- Sheaf.Paper.DerivedPullbackTensorIso: WeilConjectures.derivedPullbackTensorIso;
  read the four canonical comparisons, the full theorem signature and proof docstring.
  This is imported for the proof's comparison naturality input.
- Mathlib.CategoryTheory.ComposableArrows.Basic: ComposableArrows, mk₃, mk₄, hom,
  and morphisms as natural transformations. These encode the componentwise diagram
  maps without defining a new category of diagrams.

Edge cases checked: j or g identity; K or L zero; the empty scheme through its supplied
coefficient category; noninvertible e and pi; unbounded finite tensor intermediates;
completed integral tensor; identity and arbitrary endpoint comparisons; arbitrary functor
V, including identity. The calculation only uses functoriality, tensor bifunctoriality,
and naturality, so no nonempty-object, faithfulness or invertibility hypothesis is needed.
The orientations of theta inverse and sigma were checked on both ends of z_K,d,v.

Searches made before writing:

- msearch leanfinder, "Composing open tensor exchange and proper projection exchange
  commuting squares gives compactification projection base change identity": eight
  unrelated pullback and topology hits, no exact statement.
- msearch loogle, "CategoryTheory.NatTrans, CategoryTheory.Functor": NatTrans,
  naturality, composition and extensionality declarations, no projection pasting theorem.
- msearch grep, "projection.*[Pp]asting|compactification.*projection", CategoryTheory:
  zero hits.
- msearch leansearch, "Commuting squares for every arrow in two composable chains imply
  the composites intertwine": Square.fac, CommSq, TwoSquare.hCompVCompHComp and related
  general diagram declarations, no conditional identity of the node.
- rg on Mathlib/CategoryTheory for projection/base-change and compactification/projection:
  no matching theorem. rg on WeilConjectures and Sheaf for compactification/pasting,
  projection/pasting and the exact node id: no statement of this node. The varying-ring
  proper/open pasting module is a different local-pairs construction; ProjectionMap
  contains the counit projection construction used here, not the claimed equality.
- dag/lean_names_upstream.json has no matching compactification-pasting declaration.

No statement correction, new independent definition node, or dependency repair is needed.
The auxiliary record and path definitions belong to the notation of this node, as allowed
for helpers in the owning module. All declarations are listed in lean.declarations.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
