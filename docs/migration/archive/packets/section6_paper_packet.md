# Section 6 — Paper Packet

## Lemma 6.1

- paper_id: Lemma 6.1
- object_type: lemma
- section: 6
- source_pages: [224]
- exact_statement_or_close_paraphrase: (Case analysis of a unitary.) For a 2-qubit unitary $V$, either $\exists |x\rangle : V(|x\rangle \otimes |0\rangle)$ is entangled, or $\exists |\psi\rangle : \forall |x\rangle : \exists |z\rangle : V(|x\rangle \otimes |0\rangle) = |z\rangle \otimes |\psi\rangle$, or $\exists |\psi\rangle : \forall |x\rangle : \exists |z\rangle : V(|x\rangle \otimes |0\rangle) = |\psi\rangle \otimes |z\rangle$.
- paper_dependencies_explicit: [Lemma A.23]
- paper_dependencies_implicit: none
- proof_sketch_summary: Either $\exists |x\rangle$ such that $V(|x\rangle \otimes |0\rangle)$ is entangled, or $\forall |x\rangle$ it is not entangled (hence a tensor product). In the second branch, apply Lemma A.23 to obtain either $\exists |\psi\rangle : \forall |x\rangle : \exists |z\rangle : V(|x\rangle \otimes |0\rangle) = |z\rangle \otimes |\psi\rangle$ or $\exists |\psi\rangle : \forall |x\rangle : \exists |z\rangle : V(|x\rangle \otimes |0\rangle) = |\psi\rangle \otimes |z\rangle$.
- extraction_confidence: high
- ambiguities: none

## Lemma 6.2

- paper_id: Lemma 6.2
- object_type: lemma
- section: 6
- source_pages: [224, 225, 226]
- exact_statement_or_close_paraphrase: Suppose $u_0, u_1$ are complex numbers such that $|u_0| = |u_1| = 1$. For 2-qubit unitaries $U_1, W_2, V_3, U_4$, if $U_1^{AC} W_2^{BC} V_3^{AC} U_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$, $V_3(|0\rangle \otimes |0\rangle) = |0\rangle \otimes |0\rangle$, and for any $|x_A\rangle$: $U_1^{AC}(|x_A\rangle \otimes |0_B\rangle \otimes |0_C\rangle) = U_4^{BC\dagger} V_3^{AC\dagger}(|x_A\rangle \otimes |0_B\rangle \otimes |0_C\rangle)$, then either $u_0 = u_1$ or $u_0 u_1 = 1$ or there exist 2-qubit unitaries $W_1, W_3, W_4$ and a 1-qubit unitary $P_3$ such that $U_1^{AC} W_2^{BC} V_3^{AC} U_4^{BC} = W_1^{AC} W_2^{BC} W_3^{AC} W_4^{BC}$ and $W_3 = I \otimes |0\rangle\langle 0| + P_3 \otimes |1\rangle\langle 1|$.
- paper_dependencies_explicit: [Lemma 6.1, Lemma A.10, Lemma A.12, Lemma A.19, Lemma 4.4, Lemma A.31, Lemma A.25, Lemma A.22, Lemma A.17]
- paper_dependencies_implicit: none
- proof_sketch_summary: Apply Lemma 6.1 to $V_3^\dagger$ for a three-case analysis. Case 1 (entangled): use swap-based manipulation with Lemma A.10 and A.12 to rewrite the assumption, then Lemma A.19 gives $U_4^\dagger = |0\rangle\langle 0| \otimes Q_0 + |1\rangle\langle 1| \otimes Q_1$; conclude $u_0 = u_1$ or $u_0 u_1 = 1$ via Lemma 4.4. Case 2 ($V_3^\dagger(|x\rangle \otimes |0\rangle) = |z\rangle \otimes |\psi\rangle$): Lemma A.31 directly gives the decomposition with $W_3 = I \otimes |0\rangle\langle 0| + P_3 \otimes |1\rangle\langle 1|$. Case 3 ($V_3^\dagger(|x\rangle \otimes |0\rangle) = |\psi\rangle \otimes (P_0|x\rangle)$): use Lemma A.25 for the form, derive $\forall |x\rangle : \exists |w\rangle : U_4^\dagger(|0\rangle \otimes (P_0|x\rangle)) = |0\rangle \otimes |w\rangle$ via Lemma A.22, then Lemma A.17 gives $U_4^\dagger$ in block diagonal form; conclude via Lemma 4.4.
- extraction_confidence: high
- ambiguities: none

## Lemma 6.3

- paper_id: Lemma 6.3
- object_type: lemma
- section: 6
- source_pages: [226, 227, 228]
- exact_statement_or_close_paraphrase: Suppose $u_0, u_1$ are complex numbers such that $|u_0| = |u_1| = 1$. For 2-qubit unitaries $V_1, V_2, V_3, V_4$, if $V_1^{AC} V_2^{BC} V_3^{AC} V_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$, $\exists |\psi\rangle : \forall |x\rangle : \exists |z\rangle : V_2(|x\rangle \otimes |0\rangle) = |z\rangle \otimes |\psi\rangle$, and $V_3(|0\rangle \otimes |0\rangle) = |0\rangle \otimes |0\rangle$, then either $u_0 = u_1$ or $u_0 u_1 = 1$ or there exist 2-qubit unitaries $W_1, W_2, W_3, W_4$ and 1-qubit unitaries $P_1, P_2, P_3, P_4, Q$ such that $W_1^{AC} W_2^{BC} W_3^{AC} W_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$, $W_1 = I \otimes |\beta\rangle\langle 0| + P_1 \otimes |\beta^\perp\rangle\langle 1|$, $W_2 = I \otimes |0\rangle\langle 0| + P_2 \otimes |1\rangle\langle 1|$, $W_3 = I \otimes |0\rangle\langle 0| + P_3 \otimes |1\rangle\langle 1|$, $W_4 = I \otimes |0\rangle\langle\beta| + P_4 \otimes |1\rangle\langle\beta^\perp|$, where $|\beta\rangle = Q|0\rangle$ and $|\beta^\perp\rangle = Q|1\rangle$.
- paper_dependencies_explicit: [Lemma A.30, Lemma A.29, Lemma 6.2, Lemma A.28, Lemma A.22, Lemma A.26, Lemma A.18]
- paper_dependencies_implicit: none
- proof_sketch_summary: Use Lemma A.30 on the $V_2$ assumption to rewrite the product as $U_1^{AC} W_2^{BC} V_3^{AC} U_4^{BC}$ with $W_2 = I \otimes |0\rangle\langle 0| + P_2 \otimes |1\rangle\langle 1|$. From $W_2(|0\rangle \otimes |0\rangle) = |0\rangle \otimes |0\rangle$ and Lemma A.29, derive the key identity for any $|x_A\rangle$: $U_1^{AC}(|x_A\rangle \otimes |0_B\rangle \otimes |0_C\rangle) = U_4^{BC\dagger} V_3^{AC\dagger}(|x_A\rangle \otimes |0_B\rangle \otimes |0_C\rangle)$. Apply Lemma 6.2 to get a three-way disjunction. In the third case, use Lemma A.28 to derive $\forall |z\rangle : \exists |w\rangle : W_4^\dagger(|z\rangle \otimes |0\rangle) = |z\rangle \otimes |w\rangle$ via Lemma A.22, then Lemma A.26 gives $W_4^\dagger(|z\rangle \otimes |0\rangle) = |z\rangle \otimes |\beta\rangle$. Derive $W_4 = I \otimes |0\rangle\langle\beta| + P_4 \otimes |1\rangle\langle\beta^\perp|$ using Lemma A.18. Derive $W_1 = I \otimes |\beta\rangle\langle 0| + P_1 \otimes |\beta^\perp\rangle\langle 1|$ using Lemma A.29 and Lemma A.18.
- extraction_confidence: high
- ambiguities: none

## Lemma 6.4

- paper_id: Lemma 6.4
- object_type: lemma
- section: 6
- source_pages: [228, 229, 230]
- exact_statement_or_close_paraphrase: (The second main lemma.) Suppose $u_0, u_1$ are complex numbers such that $|u_0| = |u_1| = 1$. There exist 2-qubit unitaries $U_1, U_2, U_3, U_4$ such that $U_1^{AC} U_2^{BC} U_3^{AC} U_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$ if and only if either $u_0 = u_1$ or $u_0 u_1 = 1$.
- paper_dependencies_explicit: [Lemma A.32, Lemma A.28, Lemma 6.1, Lemma A.19, Lemma 4.3, Lemma A.33, Lemma 6.3, Lemma 4.2]
- paper_dependencies_implicit: none
- proof_sketch_summary: Left-to-right: Use Lemma A.32 to obtain $V_1, V_2, V_3, V_4$ with $V_3(|0\rangle \otimes |0\rangle) = |0\rangle \otimes |0\rangle$ and $V_1^{AC} V_2^{BC} V_3^{AC} V_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$. Apply Lemma A.28 to derive $V_1^{AC} V_2^{BC}(|0_A\rangle \otimes |x_B\rangle \otimes |0_C\rangle) = V_4^{BC\dagger}(|0_A\rangle \otimes |x_B\rangle \otimes |0_C\rangle)$. Three-case analysis on $V_2$ via Lemma 6.1. Case 1 (entangled): Lemma A.19 gives $V_1 = |0\rangle\langle 0| \otimes P_0 + |1\rangle\langle 1| \otimes P_1$, then Lemma 4.3 concludes. Case 2 ($V_2(|x\rangle \otimes |0\rangle) = |\psi\rangle \otimes |z\rangle$): Lemma A.33 gives the same block-diagonal form for $V_1$, then Lemma 4.3 concludes. Case 3 ($V_2(|x\rangle \otimes |0\rangle) = |z\rangle \otimes |\psi\rangle$): apply Lemma 6.3 to get the structured decomposition with $W_1, \ldots, W_4$; compute $CC(\mathrm{Diag}(u_0, u_1)) = I \otimes I \otimes |\beta\rangle\langle\beta| + (P_1 P_3) \otimes (P_2 P_4) \otimes |\beta^\perp\rangle\langle\beta^\perp|$; conclude $u_0 = u_1$ via Lemma 4.2. Right-to-left: use the right-to-left direction of Lemma 4.3.
- extraction_confidence: high
- ambiguities: none
