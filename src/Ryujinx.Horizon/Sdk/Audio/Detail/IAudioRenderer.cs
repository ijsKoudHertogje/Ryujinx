using Ryujinx.Horizon.Common;
using Ryujinx.Horizon.Sdk.Sf;
using System;

namespace Ryujinx.Horizon.Sdk.Audio.Detail
{
    interface IAudioRenderer : IServiceObject
    {
        Result GetSampleRate(out int sampleRate);
        Result GetSampleCount(out int sampleCount);
        Result GetMixBufferCount(out int mixBufferCount);
        Result GetState(out int state);
        Result RequestUpdate(Span<byte> output, Span<byte> performanceOutput, ReadOnlySpan<byte> input);
        Result Start();
        Result Stop();
        Result QuerySystemEvent(out int eventHandle);
        Result SetRenderingTimeLimit(int percent);
        Result GetRenderingTimeLimit(out int percent);
        Result RequestUpdateAuto(Span<byte> output, Span<byte> performanceOutput, ReadOnlySpan<byte> input);
        Result ExecuteAudioRendererRendering();
        Result SetVoiceDropParameter(float voiceDropParameter);
        Result GetVoiceDropParameter(out float voiceDropParameter);
    }
}
