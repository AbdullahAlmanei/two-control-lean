# Appendix Citation Packet -- Lemma `cosinesine`

## Local Claim

- local_object_id: Lemma `cosinesine`
- object_type: lemma
- local_source_file: reference/toff_ref/main.tex
- local_label: cosinesine
- exact_statement_or_close_paraphrase: For a 2-qubit gate $V$, there exist six 1-qubit gates $P_0$, $P_1$, $R_y(\theta_0)$, $R_y(\theta_1)$, $Q_0$, and $Q_1$, and three 2-qubit gates $P = |0\rangle\langle 0| \otimes P_0 + |1\rangle\langle 1| \otimes P_1$, $R = R_y(\theta_0) \otimes |0\rangle\langle 0| + R_y(\theta_1) \otimes |1\rangle\langle 1|$, and $Q = |0\rangle\langle 0| \otimes Q_0 + |1\rangle\langle 1| \otimes Q_1$, such that the circuit equality in Lemma `cosinesine` holds, i.e. the underlying matrix factorization is $V = P R Q$.
- cited_source: Paige and Wei (1994), "History and generality of the CS decomposition"

## Cited Source Anchor

- cited_source_local_copy: reference/toff_ref/paige_wei.pdf
- cited_source_anchor: Theorem 8.1 on printed page 313, equation (15) on printed page 314, and the square-block variant developed at the start of Section 9 on printed page 315.
- cited_source_pages: [313, 314, 315]
- exact_source_statement_or_close_paraphrase: For any 2-by-2 block partitioning of a unitary matrix $Q$, there exist unitary block-diagonal matrices $U = \operatorname{diag}(U_1, U_2)$ and $W = \operatorname{diag}(W_1, W_2)$ such that $U^\dagger Q W = D$, where $D$ has cosine-sine form. In the square-block variant discussed immediately after Theorem 8.1, the core can be written in rotation form $\begin{bmatrix} \hat C & -\hat S \\ \hat S & \hat C \end{bmatrix}$ with diagonal $\hat C, \hat S$ satisfying $\hat C^2 + \hat S^2 = I$.
- source_extraction_confidence: high

## Claim-To-Source Relationship

- relationship_summary: The local lemma is the 4-by-4, 2-plus-2 block specialization of Paige-Wei's CS decomposition, rewritten from matrix language into 2-qubit gate language.
- translation_step_1: A 2-qubit gate is exactly a 4-by-4 unitary matrix. Partition $V$ into 2-by-2 blocks using the first qubit as the outer block index.
- translation_step_2: Apply Paige-Wei Theorem 8.1 to that 2-plus-2 partition. Rearranging $U^\dagger V W = D$ gives $V = U D W^\dagger$.
- translation_step_3: Rename the left block-diagonal factor as $P = \operatorname{diag}(P_0, P_1)$ with $P_0 := U_1$ and $P_1 := U_2$. Rename the right block-diagonal factor as $Q = \operatorname{diag}(Q_0, Q_1)$ with $Q_0 := W_1^\dagger$ and $Q_1 := W_2^\dagger$. This matches the local forms $|0\rangle\langle 0| \otimes P_0 + |1\rangle\langle 1| \otimes P_1$ and $|0\rangle\langle 0| \otimes Q_0 + |1\rangle\langle 1| \otimes Q_1$.
- translation_step_4: In the 2-plus-2 case, the square-block variant gives a middle factor $R_{\mathrm{CS}} = \begin{bmatrix} C & -S \\ S & C \end{bmatrix}$ where $C = \operatorname{diag}(c_0, c_1)$ and $S = \operatorname{diag}(s_0, s_1)$ are diagonal and satisfy $c_i^2 + s_i^2 = 1$ for each $i$.
- translation_step_5: Choose angles $\theta_0, \theta_1$ so that $c_i = \cos(\theta_i/2)$ and $s_i = \sin(\theta_i/2)$. Then each 2-by-2 real rotation block $\begin{bmatrix} c_i & -s_i \\ s_i & c_i \end{bmatrix}$ is exactly $R_y(\theta_i)$.
- translation_step_6: Under the computational basis ordering $|00\rangle, |01\rangle, |10\rangle, |11\rangle$, the Paige-Wei middle factor becomes

$$
R_{\mathrm{CS}}
=
\begin{bmatrix}
c_0 & 0 & -s_0 & 0 \\
0 & c_1 & 0 & -s_1 \\
s_0 & 0 & c_0 & 0 \\
0 & s_1 & 0 & c_1
\end{bmatrix}
=
R_y(\theta_0) \otimes |0\rangle\langle 0| + R_y(\theta_1) \otimes |1\rangle\langle 1|.
$$

- translation_step_7: Therefore the matrix identity furnished by the cited paper is exactly $V = P R Q$, where $R = R_y(\theta_0) \otimes |0\rangle\langle 0| + R_y(\theta_1) \otimes |1\rangle\langle 1|$. The local circuit diagram is the standard quantum-circuit presentation of that same factorization.

## What The Source Gives Directly

- direct_from_source: Existence of left and right block-diagonal unitary factors and a central cosine-sine core for any 2-by-2 block partitioned unitary matrix.
- direct_after_square_block_variant: Existence of the precise middle shape $\begin{bmatrix} \hat C & -\hat S \\ \hat S & \hat C \end{bmatrix}$ with diagonal square blocks, which is the form needed for the 2-qubit restatement.
- indirect_but_standard_translation: Reading 2-by-2 unitaries as 1-qubit gates, reading 4-by-4 block-diagonal matrices as controlled 1-qubit gates, and naming each 2-by-2 real rotation block as an $R_y(\theta_i)$ gate.

## Support Assessment

- support_verdict: supported after specialization and notation translation
- support_scope: The citation supports the appendix existence claim. The cited paper is not written in quantum-circuit language, but its CSD theorem is mathematically equivalent to the claimed factorization once the 4-by-4 unitary is interpreted as a 2-qubit gate.
- citation_sharpness_note: A sharper internal reference is "Paige and Wei 1994, Theorem 8.1 and the square-block variant at the start of Section 9" rather than a generic citation to the paper as a whole.

## Ambiguities

- ambiguities: The exact rotation-core form used in the local lemma is not packaged as a separately numbered theorem in Paige-Wei; it is obtained from Theorem 8.1 together with the Section 9 variant discussion. This is still sufficient for the local lemma because the local statement is an existence claim, not a stricter normal-form claim.